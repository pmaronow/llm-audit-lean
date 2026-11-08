import SAP.P022.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T6_L2

open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal
noncomputable section

lemma designProbability_union_of_implication (d : Design)
    (E F G : Assignment d → Prop) (h : ∀ π, E π → F π ∨ G π) :
    designProbability d E ≤ designProbability d F + designProbability d G := by
  classical
  unfold designProbability designExpectation
  rw [← Finset.expect_add_distrib]
  apply Finset.expect_le_expect
  intro π _
  by_cases hE : E π
  · rw [if_pos hE]
    rcases h π hE with hF | hG
    · simp [hF]
      split_ifs <;> norm_num
    · simp [hG]
      split_ifs <;> norm_num
  · rw [if_neg hE]
    by_cases hF : F π <;> by_cases hG : G π <;> simp [hF, hG]

lemma empiricalCDF_bounds {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ) (x : ℝ) :
    0 ≤ empiricalCDF y x ∧ empiricalCDF y x ≤ 1 := by
  simpa only [SAP.P022.Bridge.empiricalCDF_eq] using
    AronowAudit.P022.empirical_cdf_bounds hN y x

lemma lawCDF_bounds (H : JointLaw) (t : Bool) (x : ℝ) :
    0 ≤ lawCDF H t x ∧ lawCDF H t x ≤ 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · unfold lawCDF
    have hm : (H : Measure (ℝ × ℝ)) {p | (if t then p.1 else p.2) ≤ x} ≤ 1 := by
      calc
        (H : Measure (ℝ × ℝ)) {p | (if t then p.1 else p.2) ≤ x} ≤
            (H : Measure (ℝ × ℝ)) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by simp
    exact (ENNReal.toReal_mono (by simp) hm).trans_eq (by simp)

lemma cdfDistance_bdd (A B : ℝ → ℝ)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ 1) (hB : ∀ x, 0 ≤ B x ∧ B x ≤ 1) :
    BddAbove (Set.range (fun x => |A x - B x|)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [abs_sub_le_iff]
  constructor <;> linarith [(hA x).1, (hA x).2, (hB x).1, (hB x).2]

lemma cdfDistance_point (A B : ℝ → ℝ)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ 1) (hB : ∀ x, 0 ≤ B x ∧ B x ≤ 1) (x : ℝ) :
    |A x - B x| ≤ cdfDistance A B :=
  le_csSup (cdfDistance_bdd A B hA hB) (Set.mem_range_self x)

lemma cdfDistance_triangle (A P L : ℝ → ℝ)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ 1) (hP : ∀ x, 0 ≤ P x ∧ P x ≤ 1)
    (hL : ∀ x, 0 ≤ L x ∧ L x ≤ 1) :
    cdfDistance A P ≤ cdfDistance L A + cdfDistance L P := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  calc
    |A x - P x| ≤ |A x - L x| + |L x - P x| := abs_sub_le _ _ _
    _ = |L x - A x| + |L x - P x| := by rw [abs_sub_comm (A x)]
    _ ≤ cdfDistance L A + cdfDistance L P :=
      add_le_add (cdfDistance_point L A hL hA x) (cdfDistance_point L P hL hP x)

lemma ennreal_boundedUnder_of_limsup_ne_top {α : Type*} (f : Filter α)
    (u : α → ℝ≥0∞) (h : Filter.limsup u f ≠ ⊤) :
    f.IsBoundedUnder (· ≤ ·) u := by
  change ∃ b, ∀ᶠ x in f, u x ≤ b
  by_contra hbound
  have hset : {b : ℝ≥0∞ | ∀ᶠ x in f, u x ≤ b} = ∅ := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hb
    exact hbound ⟨b, hb⟩
  have htop : Filter.limsup u f = ⊤ := by
    simp only [Filter.limsup, Filter.limsSup, Filter.eventually_map]
    rw [hset]
    exact sInf_empty
  exact h htop

end
end SAP.P022.WH.W1.P.T6_L2

open SAP.P022.WH.W1.P.T6_L2
open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

theorem SAP.P022.WH.W1.T6_L2_proof : SAP.P022.WH.W1.T6_L2 := by
  intro hRates
  change UpperLastLimit
  intro S H θ ρ C hcond hC hy hLemma ε1 ξ hε1 hξ hξlt
  let a : ℝ := ε1 / (16 * C ^ 2)
  let η : ℝ := a - ξ
  have hη : 0 < η := by
    dsimp [η, a]
    have hden : 0 < 16 * C ^ 2 := by positivity
    have hbase : 0 < ε1 / (16 * C ^ 2) := div_pos hε1 hden
    linarith
  have hsmall : Tendsto (fun q : ℕ => a / ((S.design q).N : ℝ)) atTop (𝓝 0) := by
    have hshift : Tendsto (fun q : ℕ => q + 4) atTop atTop :=
      (tendsto_add_atTop_iff_nat 4).2 tendsto_id
    simpa only [S.size, Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat a).comp hshift
  have hpop : ∀ t : Bool, ∀ᶠ q : ℕ in atTop,
      cdfDistance (lawCDF H t) (empiricalCDF (rowOutcomes S t q)) +
        a / ((S.design q).N : ℝ) < ξ := by
    intro t
    have ht : Tendsto (fun q : ℕ =>
        cdfDistance (lawCDF H t) (empiricalCDF (rowOutcomes S t q)) +
          a / ((S.design q).N : ℝ)) atTop (𝓝 0) := by
      simpa only [zero_add] using (hLemma.1 t).add hsmall
    exact ht.eventually (gt_mem_nhds hξ)
  let lastEvent : (q : ℕ) → Assignment (S.design q) → Prop := fun q π =>
    ε1 / 2 ≤ |lastIntegralTerm (S.design q) (rowOutcomes S true q)
      (rowOutcomes S false q) C π|
  let tailT : (q : ℕ) → Assignment (S.design q) → Prop := fun q π =>
    η ≤ cdfDistance (lawCDF H true) (sampledCDF S true q π)
  let tailC : (q : ℕ) → Assignment (S.design q) → Prop := fun q π =>
    η ≤ cdfDistance (lawCDF H false) (sampledCDF S false q π)
  have hinclude : ∀ᶠ q : ℕ in atTop, ∀ π, lastEvent q π → tailT q π ∨ tailC q π := by
    filter_upwards [hpop true, hpop false] with q hpopT hpopC
    intro π hlarge
    let d := S.design q
    have hNnat : 0 < d.N := by have := d.population_min; omega
    have hN : 0 < (d.N : ℝ) := by exact_mod_cast hNnat
    have hm : 0 < d.m := by have := d.treatment_min; omega
    have hk : 0 < d.k := by have := d.control_min; omega
    have hthreshold : ((d.N : ℝ) - 1) * (ε1 / 2) / (8 * d.N * C ^ 2) =
        a - a / (d.N : ℝ) := by
      dsimp [a]
      field_simp [ne_of_gt hC, ne_of_gt hN]
      <;> ring
    have hcases := (SAP.P022.Bridge.proposition2_corrected_finite_proof
      d (rowOutcomes S true q) (rowOutcomes S false q) C hC.le
      (fun i => hy i)).2.2.2 (ε1 / 2) (by positivity) π hlarge
    rw [hthreshold] at hcases
    have hpopT' : cdfDistance (lawCDF H true)
        (empiricalCDF (rowOutcomes S true q)) + a / (d.N : ℝ) < ξ := by
      simpa [d] using hpopT
    have hpopC' : cdfDistance (lawCDF H false)
        (empiricalCDF (rowOutcomes S false q)) + a / (d.N : ℝ) < ξ := by
      simpa [d] using hpopC
    rcases hcases with hT | hC'
    · have htri := cdfDistance_triangle
        (empiricalCDF (observedTreatment d (rowOutcomes S true q) π))
        (empiricalCDF (rowOutcomes S true q)) (lawCDF H true)
        (fun x => empiricalCDF_bounds hm _ x) (fun x => empiricalCDF_bounds hNnat _ x)
        (lawCDF_bounds H true)
      have htri' : cdfDistance
          (empiricalCDF (observedTreatment d (rowOutcomes S true q) π))
          (empiricalCDF (rowOutcomes S true q)) ≤
          cdfDistance (lawCDF H true)
            (empiricalCDF (observedTreatment d (rowOutcomes S true q) π)) +
          cdfDistance (lawCDF H true) (empiricalCDF (rowOutcomes S true q)) := htri
      have hD : a - ξ ≤ cdfDistance (lawCDF H true)
          (empiricalCDF (observedTreatment d (rowOutcomes S true q) π)) := by
        linarith [hT, htri', hpopT']
      have hTail : η ≤ cdfDistance (lawCDF H true)
          (empiricalCDF (observedTreatment d (rowOutcomes S true q) π)) := by
        simpa [η] using hD
      exact Or.inl (by simpa [tailT, sampledCDF] using hTail)
    · have htri := cdfDistance_triangle
        (empiricalCDF (observedControl d (rowOutcomes S false q) π))
        (empiricalCDF (rowOutcomes S false q)) (lawCDF H false)
        (fun x => empiricalCDF_bounds hk _ x) (fun x => empiricalCDF_bounds hNnat _ x)
        (lawCDF_bounds H false)
      have htri' : cdfDistance
          (empiricalCDF (observedControl d (rowOutcomes S false q) π))
          (empiricalCDF (rowOutcomes S false q)) ≤
          cdfDistance (lawCDF H false)
            (empiricalCDF (observedControl d (rowOutcomes S false q) π)) +
          cdfDistance (lawCDF H false) (empiricalCDF (rowOutcomes S false q)) := htri
      have hD : a - ξ ≤ cdfDistance (lawCDF H false)
          (empiricalCDF (observedControl d (rowOutcomes S false q) π)) := by
        linarith [hC', htri', hpopC']
      have hTail : η ≤ cdfDistance (lawCDF H false)
          (empiricalCDF (observedControl d (rowOutcomes S false q) π)) := by
        simpa [η] using hD
      exact Or.inr (by simpa [tailC, sampledCDF] using hTail)
  let uLast : ℕ → ℝ≥0∞ := fun q => ENNReal.ofReal
    ((S.design q).N * designProbability (S.design q) (lastEvent q))
  let uT : ℕ → ℝ≥0∞ := fun q => ENNReal.ofReal
    ((S.design q).N * designProbability (S.design q) (tailT q))
  let uC : ℕ → ℝ≥0∞ := fun q => ENNReal.ofReal
    ((S.design q).N * designProbability (S.design q) (tailC q))
  let rT := marginalTailRate θ ρ true η
  let rC := marginalTailRate θ ρ false η
  have hrT : Filter.limsup uT atTop ≤ ENNReal.ofReal rT := by
    have hh := hRates.2.2 S H θ ρ hcond hLemma true η hη
    change Filter.limsup uT atTop ≤ ENNReal.ofReal rT at hh
    exact hh
  have hrC : Filter.limsup uC atTop ≤ ENNReal.ofReal rC := by
    have hh := hRates.2.2 S H θ ρ hcond hLemma false η hη
    change Filter.limsup uC atTop ≤ ENNReal.ofReal rC at hh
    exact hh
  have rTnonneg : 0 ≤ rT := by
    rcases hcond with ⟨hθ, hθ1, hρ, hρ1, _⟩
    exact marginal_rate_nonneg θ ρ hθ hθ1 hρ hρ1 true η
  have rCnonneg : 0 ≤ rC := by
    rcases hcond with ⟨hθ, hθ1, hρ, hρ1, _⟩
    exact marginal_rate_nonneg θ ρ hθ hθ1 hρ hρ1 false η
  have hTbounded : atTop.IsBoundedUnder (· ≤ ·) uT :=
    ennreal_boundedUnder_of_limsup_ne_top atTop uT
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hrT)
  have hCbounded : atTop.IsBoundedUnder (· ≤ ·) uC :=
    ennreal_boundedUnder_of_limsup_ne_top atTop uC
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hrC)
  have hpoint : ∀ᶠ q : ℕ in atTop, uLast q ≤ uT q + uC q := by
    filter_upwards [hinclude] with q hq
    have hprob := designProbability_union_of_implication (S.design q)
      (lastEvent q) (tailT q) (tailC q) (hq)
    have hN : 0 ≤ ((S.design q).N : ℝ) := Nat.cast_nonneg _
    have hpt : 0 ≤ designProbability (S.design q) (tailT q) := by
      unfold designProbability designExpectation
      exact Finset.expect_nonneg (by intro π _; split_ifs <;> norm_num)
    have hpc : 0 ≤ designProbability (S.design q) (tailC q) := by
      unfold designProbability designExpectation
      exact Finset.expect_nonneg (by intro π _; split_ifs <;> norm_num)
    have hreal := mul_le_mul_of_nonneg_left hprob hN
    change ENNReal.ofReal ((S.design q).N *
        designProbability (S.design q) (lastEvent q)) ≤ _
    calc
      _ ≤ ENNReal.ofReal ((S.design q).N *
          (designProbability (S.design q) (tailT q) +
            designProbability (S.design q) (tailC q))) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal ((S.design q).N *
            designProbability (S.design q) (tailT q)) +
          ENNReal.ofReal ((S.design q).N *
            designProbability (S.design q) (tailC q)) := by
        rw [show (S.design q).N *
            (designProbability (S.design q) (tailT q) +
              designProbability (S.design q) (tailC q)) =
            (S.design q).N * designProbability (S.design q) (tailT q) +
              (S.design q).N * designProbability (S.design q) (tailC q) by ring]
        exact ENNReal.ofReal_add (mul_nonneg hN hpt) (mul_nonneg hN hpc)
      _ = uT q + uC q := rfl
  have hT1 : ∀ᶠ q : ℕ in atTop, uT q < ENNReal.ofReal (rT + 1) := by
    have hlt : ENNReal.ofReal rT < ENNReal.ofReal (rT + 1) := by
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < rT + 1)).2 (by linarith)
    have hh := Filter.eventually_lt_of_limsup_lt (hrT.trans_lt hlt) hTbounded
    have hadd : ENNReal.ofReal rT + ENNReal.ofReal 1 = ENNReal.ofReal (rT + 1) :=
      (ENNReal.ofReal_add rTnonneg (by norm_num)).symm
    simpa only [hadd] using hh
  have hC1 : ∀ᶠ q : ℕ in atTop, uC q < ENNReal.ofReal (rC + 1) := by
    have hlt : ENNReal.ofReal rC < ENNReal.ofReal (rC + 1) := by
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < rC + 1)).2 (by linarith)
    have hh := Filter.eventually_lt_of_limsup_lt (hrC.trans_lt hlt) hCbounded
    have hadd : ENNReal.ofReal rC + ENNReal.ofReal 1 = ENNReal.ofReal (rC + 1) :=
      (ENNReal.ofReal_add rCnonneg (by norm_num)).symm
    simpa only [hadd] using hh
  have hLastBound : atTop.IsBoundedUnder (· ≤ ·) uLast := by
    change ∃ b, ∀ᶠ q : ℕ in atTop, uLast q ≤ b
    refine ⟨ENNReal.ofReal (rT + 1) + ENNReal.ofReal (rC + 1), ?_⟩
    filter_upwards [hpoint, hT1, hC1] with q hq hT hC'
    exact hq.trans (add_le_add (le_of_lt hT) (le_of_lt hC'))
  change Filter.limsup uLast atTop ≤ ENNReal.ofReal (rT + rC)
  apply (Filter.limsup_le_iff' (h₂ := hLastBound)).2
  intro z hz
  · by_cases hzTop : z = ⊤
    · filter_upwards with q
      simp [hzTop]
    · have hR : rT + rC < z.toReal := by
        exact (ENNReal.ofReal_lt_iff_lt_toReal (add_nonneg rTnonneg rCnonneg) hzTop).mp hz
      let δ : ℝ := (z.toReal - (rT + rC)) / 3
      have hδ : 0 < δ := by dsimp [δ]; linarith
      have hTδ : ∀ᶠ q : ℕ in atTop, uT q < ENNReal.ofReal (rT + δ) := by
        have hlt : ENNReal.ofReal rT < ENNReal.ofReal (rT + δ) := by
          exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < rT + δ)).2 (by linarith)
        have hh := Filter.eventually_lt_of_limsup_lt (hrT.trans_lt hlt) hTbounded
        have hadd : ENNReal.ofReal rT + ENNReal.ofReal δ = ENNReal.ofReal (rT + δ) :=
          (ENNReal.ofReal_add rTnonneg hδ.le).symm
        simpa only [hadd] using hh
      have hCδ : ∀ᶠ q : ℕ in atTop, uC q < ENNReal.ofReal (rC + δ) := by
        have hlt : ENNReal.ofReal rC < ENNReal.ofReal (rC + δ) := by
          exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < rC + δ)).2 (by linarith)
        have hh := Filter.eventually_lt_of_limsup_lt (hrC.trans_lt hlt) hCbounded
        have hadd : ENNReal.ofReal rC + ENNReal.ofReal δ = ENNReal.ofReal (rC + δ) :=
          (ENNReal.ofReal_add rCnonneg hδ.le).symm
        simpa only [hadd] using hh
      have hsum : ENNReal.ofReal (rT + δ) + ENNReal.ofReal (rC + δ) < z := by
        have hreal : rT + δ + (rC + δ) < z.toReal := by
          dsimp [δ]
          linarith
        have hreal_nonneg : 0 ≤ rT + δ := by linarith
        have hreal'_nonneg : 0 ≤ rC + δ := by linarith
        rw [← ENNReal.ofReal_add hreal_nonneg hreal'_nonneg]
        rw [← ENNReal.ofReal_toReal hzTop]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < z.toReal)).2 hreal
      filter_upwards [hpoint, hTδ, hCδ] with q hq hT hC'
      exact ((hq.trans_lt (ENNReal.add_lt_add hT hC')).trans_le hsum.le).le
