import SAP.P022.WH.W1.Leaves
import AronowAudit.P022.Wave1.Gap.TailBCorollaryCoverage
import AronowAudit.P061.P061_Foundations
import AronowAudit.P053.P053_NormalQuantiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T17_L2

open SAP.P022 Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal NNReal
noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def SAPDesignTendsto {E : Type} [PseudoMetricSpace E] (d : ℕ → SAP.P022.Design)
    (X : (q : ℕ) → SAP.P022.Assignment (d q) → E) (x : E) : Prop :=
  ∀ ε > 0, Tendsto (fun q => SAP.P022.designProbability (d q)
    (fun π => ε ≤ dist (X q π) x)) atTop (𝓝 0)

theorem sap_designProbability_mono (d : SAP.P022.Design)
    (A B : SAP.P022.Assignment d → Prop) (hAB : ∀ π, A π → B π) :
    SAP.P022.designProbability d A ≤ SAP.P022.designProbability d B := by
  classical
  unfold SAP.P022.designProbability SAP.P022.designExpectation
  apply Finset.expect_le_expect
  intro π _
  by_cases hA : A π
  · simp [hA, hAB π hA]
  · simp only [hA, ite_false]
    split_ifs <;> norm_num

theorem sap_designProbability_union (d : SAP.P022.Design)
    (A B : SAP.P022.Assignment d → Prop) :
    SAP.P022.designProbability d (fun π => A π ∨ B π) ≤
      SAP.P022.designProbability d A + SAP.P022.designProbability d B := by
  classical
  unfold SAP.P022.designProbability SAP.P022.designExpectation
  rw [← Finset.expect_add_distrib]
  apply Finset.expect_le_expect
  intro π _
  by_cases hA : A π <;> by_cases hB : B π <;> simp [hA, hB]

theorem sap_designProbability_nonneg (d : SAP.P022.Design)
    (E : SAP.P022.Assignment d → Prop) : 0 ≤ SAP.P022.designProbability d E := by
  classical
  unfold SAP.P022.designProbability SAP.P022.designExpectation
  apply Finset.expect_nonneg
  intro π _
  split_ifs <;> norm_num

theorem SAPDesignTendsto.deterministic {E : Type} [PseudoMetricSpace E]
    (d : ℕ → SAP.P022.Design) {x : ℕ → E} {a : E}
    (hx : Tendsto x atTop (𝓝 a)) :
    SAPDesignTendsto d (fun q _ => x q) a := by
  intro ε hε
  have he := (tendsto_iff_dist_tendsto_zero.mp hx).eventually_lt_const hε
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with q hq
  simp [SAP.P022.designProbability, SAP.P022.designExpectation, not_le.mpr hq]

theorem SAPDesignTendsto.prod {E F : Type} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {d : ℕ → SAP.P022.Design}
    {X : (q : ℕ) → SAP.P022.Assignment (d q) → E}
    {Y : (q : ℕ) → SAP.P022.Assignment (d q) → F} {a : E} {b : F}
    (hX : SAPDesignTendsto d X a) (hY : SAPDesignTendsto d Y b) :
    SAPDesignTendsto d (fun q π => (X q π, Y q π)) (a, b) := by
  intro ε hε
  apply squeeze_zero (fun _ => Finset.expect_nonneg (fun _ _ => by split_ifs <;> norm_num))
    (fun q => ?_) (by simpa only [zero_add] using (hX ε hε).add (hY ε hε))
  calc
    _ ≤ SAP.P022.designProbability (d q) (fun π =>
        ε ≤ dist (X q π) a ∨ ε ≤ dist (Y q π) b) :=
      sap_designProbability_mono (d q) _ _ (fun π hp => by
        simpa only [Prod.dist_eq, le_max_iff] using hp)
    _ ≤ _ := sap_designProbability_union (d q) _ _

theorem SAPDesignTendsto.comp {E F : Type} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {d : ℕ → SAP.P022.Design}
    {X : (q : ℕ) → SAP.P022.Assignment (d q) → E} {a : E}
    (hX : SAPDesignTendsto d X a) (f : E → F) (hf : ContinuousAt f a) :
    SAPDesignTendsto d (fun q π => f (X q π)) (f a) := by
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hf ε hε
  apply squeeze_zero (fun _ => Finset.expect_nonneg (fun _ _ => by split_ifs <;> norm_num))
    (fun q => sap_designProbability_mono (d q) _ _ (fun π hp => ?_)) (hX δ hδ)
  by_contra hh
  exact (not_lt.mpr hp) (hd (lt_of_not_ge hh))

theorem sap_uniformProbability_eq (d : SAP.P022.Design)
    (E : SAP.P022.Assignment d → Prop) :
    AronowAudit.P061.probability
      (AronowAudit.P061.uniformDesign (SAP.P022.Assignment d)) E =
      SAP.P022.designProbability d E := by
  classical
  unfold AronowAudit.P061.probability SAP.P022.designProbability
    AronowAudit.P061.uniformDesign SAP.P022.designExpectation
  rw [tsum_fintype, Fintype.expect_eq_sum_div_card, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro π _
  by_cases hE : E π <;> simp [hE, one_div]

theorem sap_uniformExpectation_eq (d : SAP.P022.Design)
    (f : SAP.P022.Assignment d → ℝ) :
    AronowAudit.P061.expectation
      (AronowAudit.P061.uniformDesign (SAP.P022.Assignment d)) f =
      SAP.P022.designExpectation d f := by
  classical
  simp only [AronowAudit.P061.expectation, AronowAudit.P061.uniformDesign,
    tsum_fintype, ← Finset.mul_sum, SAP.P022.designExpectation,
    Fintype.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm]
  rw [Finset.sum_mul]

theorem SAPDesignTendsto.toP061 {S : SAP.P022.ExperimentSequence}
    (X : (q : ℕ) → SAP.P022.Assignment (S.design q) → ℝ) (a : ℝ)
    (hX : SAPDesignTendsto S.design X a) :
    AronowAudit.P061.ConvergesInProbability
      (fun q => AronowAudit.P061.uniformDesign (SAP.P022.Assignment (S.design q))) X a := by
  intro ε hε
  apply squeeze_zero
    (fun _ => AronowAudit.P061.probability_nonneg _ _)
    (fun q => AronowAudit.P061.completion_probability_mono
      (AronowAudit.P061.uniformDesign (SAP.P022.Assignment (S.design q)))
      (fun π => |X q π - a| > ε) (fun π => ε ≤ |X q π - a|) (fun π hp => by
      change ε < |X q π - a| at hp
      exact le_of_lt hp))
    (by simpa only [sap_uniformProbability_eq, Real.dist_eq] using hX ε hε)

theorem weakConverges_div_const {Ω : ℕ → Type} (D : ∀ q, AronowAudit.P061.Design (Ω q))
    (X : ∀ q, Ω q → ℝ) (L : Measure ℝ) [IsProbabilityMeasure L]
    (hX : AronowAudit.P061.WeakConverges D X L) (c : ℝ) :
    AronowAudit.P061.WeakConverges D (fun q z => X q z / c)
      (L.map (fun x : ℝ => x / c)) := by
  intro f
  let g : ℝ → ℝ := fun x => x / c
  have hg : Continuous g := by fun_prop
  have hm : Measurable g := hg.measurable
  have htest := hX (f.compContinuous ⟨g, hg⟩)
  have hmap : ∫ x, f x ∂L.map g = ∫ x, f (g x) ∂L := by
    rw [MeasureTheory.integral_map hm.aemeasurable f.continuous.aestronglyMeasurable]
  have hfun : (fun q => AronowAudit.P061.expectation (D q)
      (fun z => f (X q z / c))) =
      (fun q => AronowAudit.P061.expectation (D q)
        (fun z => (f.compContinuous ⟨g, hg⟩) (X q z))) := by
    funext q
    congr 1
  rw [hfun]
  rw [hmap]
  simpa [g] using htest

theorem scaled_normal_interval_mass (a : ℝ) (ha : 0 < a) :
    (((gaussianReal 0 1).map (fun x : ℝ => x / a)) (Icc (-1) 1)).toReal =
      2 * normalCDF a - 1 := by
  let g : ℝ → ℝ := fun x => x / a
  have hm : Measurable g := by fun_prop
  have hpre : g ⁻¹' Icc (-1) 1 = Icc (-a) a := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨hx, hy⟩
      constructor
      · have hx' := (le_div_iff₀ ha).mp hx
        linarith
      · have hy' := (div_le_iff₀ ha).mp hy
        linarith
    · rintro ⟨hx, hy⟩
      constructor
      · exact (le_div_iff₀ ha).mpr (by nlinarith)
      · exact (div_le_iff₀ ha).mpr (by nlinarith)
  rw [Measure.map_apply hm measurableSet_Icc, hpre]
  exact AronowAudit.P022.Wave1.tb13_normal_mass a (le_of_lt ha)

theorem scaled_normal_singletons_zero (a : ℝ) (ha : 0 < a) :
    (gaussianReal 0 1).map (fun x : ℝ => x / a) {1} = 0 ∧
    (gaussianReal 0 1).map (fun x : ℝ => x / a) {-1} = 0 := by
  let g : ℝ → ℝ := fun x => x / a
  have hm : Measurable g := by fun_prop
  letI : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  have hplus : g ⁻¹' ({1} : Set ℝ) = {a} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      have hx' := (div_eq_iff (ne_of_gt ha)).mp hx
      linarith
    · rintro rfl
      exact div_self (ne_of_gt ha)
  have hminus : g ⁻¹' ({-1} : Set ℝ) = {-a} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      have hx' := (div_eq_iff (ne_of_gt ha)).mp hx
      linarith
    · rintro rfl
      dsimp [g]
      rw [neg_div, div_self (ne_of_gt ha)]
  constructor
  · rw [Measure.map_apply hm (measurableSet_singleton 1), hplus, measure_singleton]
  · rw [Measure.map_apply hm (measurableSet_singleton (-1)), hminus, measure_singleton]

theorem standard_normal_cdf_zero : normalCDF 0 = 1 / 2 := by
  change (gaussianReal 0 1).real (Iic 0) = 1 / 2
  rw [← cdf_eq_real]
  exact AronowAudit.P053.NormalCompletion.normal_cdf_zero

end
end SAP.P022.WH.W1.P.T17_L2

open SAP.P022 SAP.P022.Bridge SAP.P022.WH.W1.P.T17_L2
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal NNReal

theorem SAP.P022.WH.W1.T17_L2_proof : SAP.P022.WH.W1.T17_L2 := by
  classical
  intro S H θ ρ h h3 hns W v hW hv hconv α hα hα1
  let S' := SAP.P022.Bridge.toSequence S
  have h' : AronowAudit.P022.Conditions123 S' H θ ρ := by
    simpa only [S', SAP.P022.Bridge.Conditions123_eq] using h
  have h3' : AronowAudit.P022.BoundedThirdMoments S' := by
    simpa only [S', SAP.P022.Bridge.BoundedThirdMoments_eq] using h3
  have hns' : AronowAudit.P022.NonsingularLaw H := by
    simpa only [SAP.P022.Bridge.NonsingularLaw_eq] using hns
  have hUI := AronowAudit.P022.Wave1.tb13_square_integrability S' h3'
  have hsA : 0 < AronowAudit.P022.limitingTrueVariance H θ ρ :=
    AronowAudit.P022.Wave1.tb13_limiting_variance_pos S' H θ ρ h' hUI hns'
  have hs : 0 < limitingTrueVariance H θ ρ := by
    simpa only [SAP.P022.Bridge.limitingTrueVariance_eq] using hsA
  have hvlim := AronowAudit.P022.Wave1.tb13_true_variance_limit S' H θ ρ h' hUI
  have hz : 0 < normalCritical α :=
    AronowAudit.P053.NormalCompletion.normalCritical_pos α hα hα1
  let V (q : ℕ) := trueVariance (S.design q)
    (rowOutcomes S true q) (rowOutcomes S false q)
  let E (q : ℕ) (π : Assignment (S.design q)) := effectError S q π
  let A (q : ℕ) (π : Assignment (S.design q)) := rowSize S q * W q π
  let B (q : ℕ) := rowSize S q * V q
  let z := normalCritical α
  have hVlim : Tendsto B atTop (𝓝 (limitingTrueVariance H θ ρ)) := by
    simpa only [S', B, rowSize, V, SAP.P022.Bridge.toSequence_design,
      SAP.P022.Bridge.toDesign_N, SAP.P022.Bridge.trueVariance_eq,
      SAP.P022.Bridge.rowOutcomes_eq, SAP.P022.Bridge.limitingTrueVariance_eq] using hvlim
  have hA : SAPDesignTendsto S.design A v := by
    intro ε hε
    simpa only [A, Real.dist_eq, abs_sub_comm] using hconv ε hε
  have hB : SAPDesignTendsto S.design (fun q _ => B q)
      (limitingTrueVariance H θ ρ) :=
    SAPDesignTendsto.deterministic S.design hVlim
  have hAB := hA.prod hB
  let F (p : ℝ × ℝ) := z * Real.sqrt p.1 / Real.sqrt p.2
  have hFcont : ContinuousAt F (v, limitingTrueVariance H θ ρ) := by
    dsimp [F]
    exact (continuousAt_const.mul
      (Real.continuous_sqrt.continuousAt.comp continuousAt_fst)).div
      (Real.continuous_sqrt.continuousAt.comp continuousAt_snd)
      (Real.sqrt_pos.mpr hs).ne'
  let R (q : ℕ) (π : Assignment (S.design q)) :=
    z * Real.sqrt (W q π) / Real.sqrt (V q)
  let a := z * Real.sqrt (v / limitingTrueVariance H θ ρ)
  have hBpos : ∀ᶠ q in atTop, 0 < B q :=
    hVlim.eventually (eventually_gt_nhds hs)
  have hR : SAPDesignTendsto S.design R a := by
    have hscaled := hAB.comp F hFcont
    have hlimit : z * Real.sqrt v / Real.sqrt (limitingTrueVariance H θ ρ) = a := by
      dsimp [a]
      rw [Real.sqrt_div hv]
      ring
    have hscaled' : SAPDesignTendsto S.design
        (fun q π => F (A q π, B q)) a := by
      simpa only [F, hlimit] using hscaled
    have hevent : ∀ᶠ q in atTop, ∀ π, R q π = F (A q π, B q) := by
      filter_upwards [hBpos] with q hq π
      have hN : 0 < rowSize S q := size_pos S q
      have hV : 0 < V q := by
        have hq' : 0 < rowSize S q * V q := by simpa only [B] using hq
        nlinarith
      have hNcast : (0 : ℝ) ≤ rowSize S q := hN.le
      have hw := hW q π
      have hsN : 0 < Real.sqrt (rowSize S q) := Real.sqrt_pos.mpr hN
      have hVroot : 0 < Real.sqrt (V q) := Real.sqrt_pos.mpr hV
      change z * Real.sqrt (W q π) / Real.sqrt (V q) =
        z * Real.sqrt (rowSize S q * W q π) / Real.sqrt (rowSize S q * V q)
      rw [Real.sqrt_mul hNcast, Real.sqrt_mul hNcast]
      field_simp [ne_of_gt hsN, ne_of_gt hVroot]
    intro ε hε
    apply (hscaled' ε hε).congr'
    filter_upwards [hevent] with q hq
    congr 1
    funext π
    rw [hq π]

  let D : ∀ q : ℕ, AronowAudit.P061.Design (Assignment (S.design q)) :=
    fun q => AronowAudit.P061.uniformDesign (Assignment (S.design q))
  have hZsap : weakStandardNormal S (fun q π => E q π / Real.sqrt (V q)) := by
    have hZ' := AronowAudit.P022.Wave1.tb13_actual_variance_clt S' H θ ρ h' h3' hns'
    rw [← SAP.P022.Bridge.weakStandardNormal_eq]
    change AronowAudit.P022.weakStandardNormal (SAP.P022.Bridge.toSequence S)
      (fun q π => (AronowAudit.P022.estimatedEffect
        ((SAP.P022.Bridge.toSequence S).design q)
        (AronowAudit.P022.rowOutcomes (SAP.P022.Bridge.toSequence S) true q)
        (AronowAudit.P022.rowOutcomes (SAP.P022.Bridge.toSequence S) false q) π -
        AronowAudit.P022.averageEffect ((SAP.P022.Bridge.toSequence S).design q)
        (AronowAudit.P022.rowOutcomes (SAP.P022.Bridge.toSequence S) true q)
        (AronowAudit.P022.rowOutcomes (SAP.P022.Bridge.toSequence S) false q)) /
        Real.sqrt (AronowAudit.P022.trueVariance ((SAP.P022.Bridge.toSequence S).design q)
          (AronowAudit.P022.rowOutcomes (SAP.P022.Bridge.toSequence S) true q)
          (AronowAudit.P022.rowOutcomes (SAP.P022.Bridge.toSequence S) false q)))
    exact hZ'
  have hZ : AronowAudit.P061.WeakConverges D
      (fun q π => E q π / Real.sqrt (V q)) (gaussianReal 0 1) := by
    intro f
    change Tendsto (fun q => AronowAudit.P061.expectation
      (AronowAudit.P061.uniformDesign (Assignment (S.design q)))
      (fun π => f (E q π / Real.sqrt (V q)))) atTop
      (𝓝 (∫ x, f x ∂gaussianReal 0 1))
    have heq : (fun q => AronowAudit.P061.expectation
        (AronowAudit.P061.uniformDesign (Assignment (S.design q)))
        (fun π => f (E q π / Real.sqrt (V q)))) =
        (fun q => designExpectation (S.design q)
          (fun π => f (E q π / Real.sqrt (V q)))) := by
      funext q
      exact sap_uniformExpectation_eq (S.design q) _
    rw [heq]
    exact hZsap f

  by_cases hvpos : 0 < v
  · have ha : 0 < a := by
      dsimp [a]
      exact mul_pos hz (Real.sqrt_pos.mpr (div_pos hvpos hs))
    have hYtail : SAPDesignTendsto S.design (fun q π => R q π / a) 1 := by
      have ht := hR.comp (fun x : ℝ => x / a) (by fun_prop)
      simpa only [div_self ha.ne'] using ht
    have hY := SAPDesignTendsto.toP061 (S := S) (fun q π => R q π / a) 1 hYtail
    have hY' : AronowAudit.P061.ConvergesInProbability D
        (fun q π => R q π / a) 1 := by simpa only [D] using hY
    let L : Measure ℝ := (gaussianReal 0 1).map (fun x : ℝ => x / a)
    have hX := weakConverges_div_const D (fun q π => E q π / Real.sqrt (V q))
      (gaussianReal 0 1) hZ a
    have hXY := AronowAudit.P061.weakConverges_div_consistent D
      (fun q π => (E q π / Real.sqrt (V q)) / a)
      (fun q π => R q π / a) L hX hY'
    have hnull := scaled_normal_singletons_zero a ha
    have hcoverage := AronowAudit.P061.weakConverges_scaled_interval D
      (fun q π => (E q π / Real.sqrt (V q)) / a)
      (fun q π => R q π / a) (fun _ => 1) L (fun _ => one_pos)
      (by simpa only [div_one] using hY') hXY 1 one_pos hnull.1 hnull.2
    have heventuallyV : ∀ᶠ q in atTop, 0 < V q := by
      filter_upwards [hBpos] with q hq
      have hN : 0 < rowSize S q := size_pos S q
      have hq' : 0 < rowSize S q * V q := by simpa only [B] using hq
      nlinarith
    have heq : ∀ᶠ q in atTop,
        waldCoverage S W α q =
          designProbability (S.design q) (fun π =>
            |(E q π / Real.sqrt (V q) / a)| ≤ R q π / a) := by
      filter_upwards [heventuallyV] with q hq
      have hVroot : 0 < Real.sqrt (V q) := Real.sqrt_pos.mpr hq
      have ha' : 0 < a := ha
      unfold waldCoverage
      congr 1
      funext π
      change (|E q π| ≤ z * Real.sqrt (W q π)) =
        (|(E q π / Real.sqrt (V q) / a)| ≤ R q π / a)
      have hleft : |(E q π / Real.sqrt (V q) / a)| =
          |E q π| / (Real.sqrt (V q) * a) := by
        rw [abs_div, abs_of_pos ha', abs_div, abs_of_pos hVroot]
        ring
      have hright : R q π / a =
          (z * Real.sqrt (W q π)) / (Real.sqrt (V q) * a) := by
        dsimp [R]
        ring
      rw [hleft, hright]
      have hd : 0 < Real.sqrt (V q) * a := mul_pos hVroot ha'
      apply propext
      constructor
      · intro h
        rw [div_le_div_iff₀ hd hd]
        exact (mul_le_mul_iff_of_pos_right hd).2 h
      · intro h
        rw [div_le_div_iff₀ hd hd] at h
        exact (mul_le_mul_iff_of_pos_right hd).1 h
    have hprob := hcoverage
    have hprob' : Tendsto (fun q => designProbability (S.design q) (fun π =>
        |(E q π / Real.sqrt (V q) / a)| ≤ R q π / a)) atTop
        (𝓝 (L (Icc (-1) 1)).toReal) := by
      simpa only [D, one_mul, sap_uniformProbability_eq] using hprob
    have hlimit : Tendsto (waldCoverage S W α) atTop
        (𝓝 (L (Icc (-1) 1)).toReal) := by
      have heq' : ∀ᶠ q in atTop,
          designProbability (S.design q) (fun π =>
            |(E q π / Real.sqrt (V q) / a)| ≤ R q π / a) =
              waldCoverage S W α q := by
        filter_upwards [heq] with q hq
        exact hq.symm
      exact hprob'.congr' heq'
    have hmass := scaled_normal_interval_mass a ha
    have hratio : a = z * Real.sqrt (v / limitingTrueVariance H θ ρ) := rfl
    have hlimit' : Tendsto (waldCoverage S W α) atTop
        (𝓝 (2 * normalCDF a - 1)) := by
      simpa only [L, hmass] using hlimit
    simpa only [gaussianWaldCoverage, hratio] using hlimit'
  · have hv0 : v = 0 := le_antisymm (le_of_not_gt hvpos) hv
    have ha0 : a = 0 := by simp [a, hv0]
    have hR0 : SAPDesignTendsto S.design R 0 := by simpa only [ha0] using hR
    have hRprob := SAPDesignTendsto.toP061 (S := S) R 0 hR0
    have hstdInterval (ε : ℝ) (hε : 0 < ε) :
        Tendsto (fun q => designProbability (S.design q) (fun π =>
          |E q π / Real.sqrt (V q)| ≤ ε)) atTop
          (𝓝 (2 * normalCDF ε - 1)) := by
      letI : NullSingletonClass (gaussianReal 0 1) :=
        nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
      have hI := AronowAudit.P061.weakConverges_abs_le D
        (fun q π => E q π / Real.sqrt (V q)) (gaussianReal 0 1) hZ ε hε
        (measure_singleton _) (measure_singleton _)
      rw [AronowAudit.P022.Wave1.tb13_normal_mass ε hε.le] at hI
      simpa only [D, sap_uniformProbability_eq, SAP.P022.Bridge.normalCDF_eq] using hI
    have hsmallmass : ∀ δ > 0, ∃ ε > 0, 2 * normalCDF ε - 1 < δ := by
      intro δ hδ
      letI : NullSingletonClass (gaussianReal 0 1) :=
        nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
      have hcdf : ContinuousAt normalCDF 0 := by
        have hc := AronowAudit.P053.NormalCompletion.cdf_continuousAt
          (gaussianReal 0 1) 0
        have heq : normalCDF = cdf (gaussianReal 0 1) := by
          funext x
          rw [normalCDF, ← measureReal_def, ← cdf_eq_real]
        rw [heq]
        exact hc
      have hmcont : ContinuousAt (fun x : ℝ => 2 * normalCDF x - 1) 0 :=
        (continuousAt_const.mul hcdf).sub continuousAt_const
      obtain ⟨r, hr, hclose⟩ := Metric.continuousAt_iff.mp hmcont
        (δ / 2) (half_pos hδ)
      let ε := r / 2
      have hε : 0 < ε := half_pos hr
      have hdist : dist ε 0 < r := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hε]
        dsimp [ε]
        linarith
      have hnear := hclose hdist
      have hmass := AronowAudit.P022.Wave1.tb13_normal_mass ε hε.le
      have hmassNonneg : 0 ≤ 2 * normalCDF ε - 1 := by
        rw [← SAP.P022.Bridge.normalCDF_eq ε]
        rw [← hmass]
        exact ENNReal.toReal_nonneg
      have hnear' : |(2 * normalCDF ε - 1) - 0| < δ / 2 := by
        simpa [Real.dist_eq, standard_normal_cdf_zero] using hnear
      refine ⟨ε, hε, ?_⟩
      have habs := abs_lt.mp hnear'
      linarith
    have htends0 : Tendsto (waldCoverage S W α) atTop (𝓝 0) := by
      apply tendsto_order.mpr
      constructor
      · intro b hb
        filter_upwards [] with q
        have hnonneg : 0 ≤ waldCoverage S W α q := by
          unfold waldCoverage
          exact sap_designProbability_nonneg _ _
        linarith
      · intro δ hδ
        obtain ⟨ε, hε, hmass⟩ := hsmallmass (δ / 3) (by linarith)
        have hInt := hstdInterval ε hε
        have hIntEventually : ∀ᶠ q in atTop,
            designProbability (S.design q) (fun π =>
              |E q π / Real.sqrt (V q)| ≤ ε) < 2 * normalCDF ε - 1 + δ / 3 :=
          hInt.eventually (Iio_mem_nhds (show
            2 * normalCDF ε - 1 < 2 * normalCDF ε - 1 + δ / 3 by linarith))
        have hBadEventually : ∀ᶠ q in atTop,
            designProbability (S.design q) (fun π => ε < |R q π|) < δ / 3 := by
          have hb : Tendsto (fun q => designProbability (S.design q)
              (fun π => ε < |R q π|)) atTop (𝓝 0) := by
            simpa only [sap_uniformProbability_eq, Real.dist_eq, sub_zero,
              abs_sub_comm] using hRprob ε hε
          exact hb.eventually (Iio_mem_nhds (show (0:ℝ) < δ/3 by linarith))
        have hVevent : ∀ᶠ q in atTop, 0 < V q := by
          filter_upwards [hBpos] with q hq
          have hN : 0 < rowSize S q := size_pos S q
          have hq' : 0 < rowSize S q * V q := by simpa only [B] using hq
          nlinarith
        filter_upwards [hIntEventually, hBadEventually, hVevent] with q hI hBad hV
        have hcoverage_event : ∀ π,
            (|E q π| ≤ z * Real.sqrt (W q π)) →
              |E q π / Real.sqrt (V q)| ≤ ε ∨ ε < |R q π| := by
          intro π hcov
          have hroot : 0 < Real.sqrt (V q) := Real.sqrt_pos.mpr hV
          have hRnonneg : 0 ≤ R q π := by
            dsimp [R]
            exact div_nonneg (mul_nonneg hz.le (Real.sqrt_nonneg _)) hroot.le
          by_cases hlarge : ε < |R q π|
          · exact Or.inr hlarge
          · left
            have hRle : R q π ≤ ε := by
              rw [abs_of_nonneg hRnonneg] at hlarge
              linarith
            have hcov' : |E q π| / Real.sqrt (V q) ≤ R q π := by
              dsimp [R]
              exact div_le_div_of_nonneg_right hcov hroot.le
            rw [abs_div, abs_of_pos hroot]
            exact le_trans hcov' hRle
        have hprobBound : waldCoverage S W α q ≤
            designProbability (S.design q) (fun π =>
              |E q π / Real.sqrt (V q)| ≤ ε) +
              designProbability (S.design q) (fun π => ε < |R q π|) := by
          unfold waldCoverage
          calc
            _ ≤ designProbability (S.design q) (fun π =>
                |E q π / Real.sqrt (V q)| ≤ ε ∨ ε < |R q π|) :=
              sap_designProbability_mono (S.design q) _ _ hcoverage_event
            _ ≤ _ := sap_designProbability_union (S.design q) _ _
        have hsmall : 2 * normalCDF ε - 1 + δ / 3 + δ / 3 < δ := by
          linarith
        have hcoverage_eq : waldCoverage S W α q = designProbability (S.design q)
            (fun π => |E q π| ≤ z * Real.sqrt (W q π)) := rfl
        rw [hcoverage_eq]
        exact lt_of_le_of_lt hprobBound (by linarith)
    have htarget : gaussianWaldCoverage α v (limitingTrueVariance H θ ρ) = 0 := by
      simp [gaussianWaldCoverage, hv0, standard_normal_cdf_zero]
    simpa only [htarget] using htends0

