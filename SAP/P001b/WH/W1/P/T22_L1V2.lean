import SAP.P001b.WH.W1.Leaves
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P001b.WH.W1.P.T22_L1V2
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical Topology
noncomputable section
variable {Ω : Type*} {E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [Countable E] [MeasurableSingletonClass E]
def cellMean (μ : Measure Ω) (X : Ω → E) (f : Ω → ℝ) (nullValue : ℝ) (x : E) : ℝ :=
  if 0 < SAP.P001b.probability μ {ω | X ω = x} then
    (∫ ω in {ω | X ω = x}, f ω ∂μ) / SAP.P001b.probability μ {ω | X ω = x}
  else nullValue
theorem cellMean_cef (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → E) (f : Ω → ℝ)
    (nullValue : ℝ) (hX : Measurable X) (hf : Integrable f μ) :
    W1CEF μ X f (cellMean μ X f nullValue) := by
  classical
  let C : E → Set Ω := fun x => {ω | X ω = x}
  have hC : ∀ x, MeasurableSet (C x) := fun x => hX (measurableSet_singleton x)
  have hdisj : Pairwise (fun x y => Disjoint (C x) (C y)) := by
    intro x y hxy
    apply Set.disjoint_left.mpr
    intro ω hx hy
    exact hxy (hx.symm.trans hy)
  have hcover : (⋃ x, C x) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨X ω, rfl⟩
  let g : Ω → ℝ := cellMean μ X f nullValue ∘ X
  have hq : HasSum (fun x : E => ∫ ω in C x, ‖f ω‖ ∂μ) (∫ ω, ‖f ω‖ ∂μ) := by
    simpa [hcover] using
      (hasSum_integral_iUnion hC hdisj hf.norm.integrableOn)
  have hqnonneg : ∀ x, 0 ≤ ∫ ω in C x, ‖f ω‖ ∂μ := by
    intro x
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hgcell : ∀ x, IntegrableOn g (C x) μ := by
    intro x
    apply (integrableOn_const (μ := μ) (s := C x)
      (C := cellMean μ X f nullValue x)).congr_fun
    · intro ω hω
      change X ω = x at hω
      simp [g, hω]
    · exact hC x
  have hcellBound : ∀ x, ∫ ω in C x, ‖g ω‖ ∂μ ≤ ∫ ω in C x, ‖f ω‖ ∂μ := by
    intro x
    have hconst : (∫ ω in C x, ‖g ω‖ ∂μ) =
        ‖cellMean μ X f nullValue x‖ * SAP.P001b.probability μ (C x) := by
      calc
        (∫ ω in C x, ‖g ω‖ ∂μ) =
            ∫ _ in C x, ‖cellMean μ X f nullValue x‖ ∂μ := by
          apply setIntegral_congr_fun (hC x)
          intro ω hω
          change X ω = x at hω
          simp [g, hω]
        _ = ‖cellMean μ X f nullValue x‖ * μ.real (C x) := by
          rw [setIntegral_const, smul_eq_mul]
          ring
        _ = ‖cellMean μ X f nullValue x‖ * SAP.P001b.probability μ (C x) := by
          rfl
    rw [hconst]
    by_cases hp : 0 < SAP.P001b.probability μ (C x)
    · have hp' : 0 < SAP.P001b.probability μ {ω | X ω = x} := by simpa [C] using hp
      have hm : cellMean μ X f nullValue x =
          (∫ ω in C x, f ω ∂μ) / SAP.P001b.probability μ (C x) := by
        simpa [cellMean, C, hp']
      rw [hm, Real.norm_eq_abs, abs_div, abs_of_pos hp]
      have htri : |∫ ω in C x, f ω ∂μ| ≤ ∫ ω in C x, ‖f ω‖ ∂μ := by
        simpa [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := μ.restrict (C x)) f)
      calc
        (|∫ ω in C x, f ω ∂μ| / SAP.P001b.probability μ (C x)) *
            SAP.P001b.probability μ (C x) = |∫ ω in C x, f ω ∂μ| :=
          div_mul_cancel₀ _ (ne_of_gt hp)
        _ ≤ ∫ ω in C x, ‖f ω‖ ∂μ := htri
    · have hp0 : SAP.P001b.probability μ (C x) = 0 :=
        le_antisymm (le_of_not_gt hp) (ENNReal.toReal_nonneg)
      have hp' : ¬ 0 < SAP.P001b.probability μ {ω | X ω = x} := by
        simpa [C] using hp
      have hm0 : cellMean μ X f nullValue x = nullValue := by
        simp [cellMean, C, hp']
      rw [hm0, Real.norm_eq_abs, hp0, mul_zero]
      exact hqnonneg x
  let q : E → ℝ := fun x => ∫ ω in C x, ‖g ω‖ ∂μ
  have hqg : Summable q := by
    apply Summable.of_nonneg_of_le
      (fun x => integral_nonneg (fun _ => norm_nonneg _))
      hcellBound hq.summable
  have hgIntOn : IntegrableOn g (⋃ x, C x) μ :=
    integrableOn_iUnion_of_summable_integral_norm hgcell hqg
  have hgInt : Integrable g μ := by
    simpa [g, hcover, IntegrableOn] using hgIntOn
  have hcellEq : ∀ x, (∫ ω in C x, f ω ∂μ) = (∫ ω in C x, g ω ∂μ) := by
    intro x
    have hgconst : (∫ ω in C x, g ω ∂μ) =
        cellMean μ X f nullValue x * SAP.P001b.probability μ (C x) := by
      calc
        (∫ ω in C x, g ω ∂μ) =
            ∫ _ in C x, cellMean μ X f nullValue x ∂μ := by
          apply setIntegral_congr_fun (hC x)
          intro ω hω
          change X ω = x at hω
          simp [g, hω]
        _ = cellMean μ X f nullValue x * μ.real (C x) := by
          rw [setIntegral_const, smul_eq_mul]
          ring
        _ = cellMean μ X f nullValue x * SAP.P001b.probability μ (C x) := rfl
    by_cases hp : 0 < SAP.P001b.probability μ (C x)
    · have hp' : 0 < SAP.P001b.probability μ {ω | X ω = x} := by simpa [C] using hp
      have hm : cellMean μ X f nullValue x =
          (∫ ω in C x, f ω ∂μ) / SAP.P001b.probability μ (C x) := by
        simpa [cellMean, C, hp']
      rw [hgconst, hm]
      exact (div_mul_cancel₀ _ (ne_of_gt hp)).symm
    · have hp0 : SAP.P001b.probability μ (C x) = 0 :=
        le_antisymm (le_of_not_gt hp) (ENNReal.toReal_nonneg)
      have hμ0 : μ (C x) = 0 := by
        apply (MeasureTheory.measureReal_eq_zero_iff).mp
        have hreal : μ.real (C x) = 0 := by
          simpa [SAP.P001b.probability, Measure.real_def] using hp0
        exact hreal
      have hp' : ¬ 0 < SAP.P001b.probability μ {ω | X ω = x} := by
        simpa [C] using hp
      rw [hgconst]
      simp [cellMean, C, hp', hp0, setIntegral_measure_zero, hμ0]
  refine ⟨measurable_of_countable _, hf, ?_, ?_⟩
  · simpa [g] using hgInt
  · intro A hA
    let s : E → Set Ω := fun x => if x ∈ A then C x else ∅
    have hs : ∀ x, MeasurableSet (s x) := by
      intro x
      by_cases hx : x ∈ A <;> simp [s, hx, hC x]
    have hsd : Pairwise (fun x y => Disjoint (s x) (s y)) := by
      intro x y hxy
      apply Set.disjoint_left.mpr
      intro ω hx hy
      by_cases hxa : x ∈ A
      · by_cases hya : y ∈ A
        · have hxC : ω ∈ C x := by simpa [s, hxa] using hx
          have hyC : ω ∈ C y := by simpa [s, hya] using hy
          exact hxy (hxC.symm.trans hyC)
        · simp [s, hya] at hy
      · simp [s, hxa] at hx
    have hscover : (⋃ x, s x) = X ⁻¹' A := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx⟩
        by_cases hxa : x ∈ A
        · have hxC : X ω = x := by simpa [s, C, hxa] using hx
          simpa [hxC] using hxa
        · simp [s, hxa] at hx
      · intro hω
        refine ⟨X ω, ?_⟩
        simp [s, C, hω]
    have hterm : ∀ x, (∫ ω in s x, f ω ∂μ) = (∫ ω in s x, g ω ∂μ) := by
      intro x
      by_cases hx : x ∈ A
      · simpa [s, hx] using hcellEq x
      · simp [s, hx]
    have hsumf : HasSum (fun x => ∫ ω in s x, f ω ∂μ)
        (∫ ω in X ⁻¹' A, f ω ∂μ) := by
      simpa [hscover] using
        (hasSum_integral_iUnion hs hsd (hf.integrableOn.mono_set (Set.subset_univ _)))
    have hsumg : HasSum (fun x => ∫ ω in s x, g ω ∂μ)
        (∫ ω in X ⁻¹' A, g ω ∂μ) := by
      simpa [hscover] using
        (hasSum_integral_iUnion hs hsd (hgInt.integrableOn.mono_set (Set.subset_univ _)))
    calc
      (∫ ω in X ⁻¹' A, f ω ∂μ) = ∑' x, ∫ ω in s x, f ω ∂μ := hsumf.tsum_eq.symm
      _ = ∑' x, ∫ ω in s x, g ω ∂μ := tsum_congr hterm
      _ = (∫ ω in X ⁻¹' A, g ω ∂μ) := hsumg.tsum_eq
theorem binary_cell_integral {Ω : Type*} {E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSingletonClass E]
    (μ : Measure Ω) (X : Ω → E) (D : Ω → ℝ) (hX : Measurable X) (hD : Measurable D)
    (hb : ∀ ω, D ω = 0 ∨ D ω = 1) (x : E) :
    (∫ ω in {ω | X ω = x}, D ω ∂μ) =
      SAP.P001b.W1JointMass μ X D 1 x := by
  let C : Set Ω := {ω | X ω = x}
  let T : Set Ω := {ω | D ω = 1}
  have hC : MeasurableSet C := hX (measurableSet_singleton x)
  have hT : MeasurableSet T := hD (measurableSet_singleton 1)
  have hEq : ∀ ω ∈ C, D ω = T.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω hω
    rcases hb ω with hz | ho
    · simp [Set.indicator, T, hz]
    · simp [Set.indicator, T, ho]
  calc
    (∫ ω in C, D ω ∂μ) = ∫ ω in C, T.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
      setIntegral_congr_fun hC hEq
    _ = ∫ ω in C ∩ T, (1 : ℝ) ∂μ := setIntegral_indicator hT
    _ = μ.real (C ∩ T) := setIntegral_one_eq_measureReal
    _ = SAP.P001b.W1JointMass μ X D 1 x := by
      have hset : C ∩ T = {ω | X ω = x ∧ D ω = 1} := by
        ext ω
        simp [C, T]
      rw [hset]
      rfl
end
end SAP.P001b.WH.W1.P.T22_L1V2
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical Topology
theorem SAP.P001b.WH.W1.T22_L1V2_proof : SAP.P001b.WH.W1.T22_L1V2 := by
  intro Ω E _ _ _ _ μ hμ X hX Y0 Y1 D hY0 hY1 hD hY0i hY1i hbin
  let S0 : Set Ω := {ω | D ω = 0}
  let S1 : Set Ω := {ω | D ω = 1}
  let obs : Ω → ℝ := fun ω => Y1 ω * D ω + Y0 ω * (1 - D ω)
  have hS0 : MeasurableSet S0 := hD (measurableSet_singleton 0)
  have hS1 : MeasurableSet S1 := hD (measurableSet_singleton 1)
  have hObs : Measurable obs := by
    dsimp [obs]
    fun_prop
  have hDint : Integrable D μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hD.aestronglyMeasurable ?_
    filter_upwards with ω
    rcases hbin ω with hz | ho
    · simp [hz]
    · simp [ho]
  have hObs0 : Integrable obs (μ.restrict S0) := by
    have h0 : Integrable Y0 (μ.restrict S0) := hY0i.mono_measure Measure.restrict_le_self
    apply h0.congr
    filter_upwards [ae_restrict_mem hS0] with ω hω
    change D ω = 0 at hω
    simp [obs, hω]
  have hObs1 : Integrable obs (μ.restrict S1) := by
    have h1 : Integrable Y1 (μ.restrict S1) := hY1i.mono_measure Measure.restrict_le_self
    apply h1.congr
    filter_upwards [ae_restrict_mem hS1] with ω hω
    change D ω = 1 at hω
    simp [obs, hω]
  have hpCEF : W1CEF μ X D (SAP.P001b.W1CellPropensity μ X D) := by
    have h := SAP.P001b.WH.W1.P.T22_L1V2.cellMean_cef μ X D (1 / 2) hX hDint
    have heq : SAP.P001b.WH.W1.P.T22_L1V2.cellMean μ X D (1 / 2) =
        SAP.P001b.W1CellPropensity μ X D := by
      funext x
      by_cases hx : 0 < SAP.P001b.probability μ {ω | X ω = x}
      · change (if 0 < SAP.P001b.probability μ {ω | X ω = x} then
            (∫ ω in {ω | X ω = x}, D ω ∂μ) /
              SAP.P001b.probability μ {ω | X ω = x} else 1 / 2) =
          (if 0 < SAP.P001b.probability μ {ω | X ω = x} then
            SAP.P001b.W1JointMass μ X D 1 x /
              SAP.P001b.probability μ {ω | X ω = x} else 1 / 2)
        rw [if_pos hx, if_pos hx]
        rw [SAP.P001b.WH.W1.P.T22_L1V2.binary_cell_integral μ X D hX hD hbin x]
      · have hp0 : SAP.P001b.probability μ {ω | X ω = x} = 0 :=
          le_antisymm (le_of_not_gt hx) (ENNReal.toReal_nonneg)
        change (if 0 < SAP.P001b.probability μ {ω | X ω = x} then
            (∫ ω in {ω | X ω = x}, D ω ∂μ) /
              SAP.P001b.probability μ {ω | X ω = x} else 1 / 2) =
          (if 0 < SAP.P001b.probability μ {ω | X ω = x} then
            SAP.P001b.W1JointMass μ X D 1 x /
              SAP.P001b.probability μ {ω | X ω = x} else 1 / 2)
        rw [if_neg hx, if_neg hx]
    rw [heq] at h
    exact h
  have harm0 : W1CEF (μ.restrict S0) X obs
      (SAP.P001b.WH.W1.P.T22_L1V2.cellMean (μ.restrict S0) X obs 0) :=
    SAP.P001b.WH.W1.P.T22_L1V2.cellMean_cef (μ.restrict S0) X obs 0 hX hObs0
  have harm1 : W1CEF (μ.restrict S1) X obs
      (SAP.P001b.WH.W1.P.T22_L1V2.cellMean (μ.restrict S1) X obs 0) :=
    SAP.P001b.WH.W1.P.T22_L1V2.cellMean_cef (μ.restrict S1) X obs 0 hX hObs1
  have hmean0 : SAP.P001b.WH.W1.P.T22_L1V2.cellMean (μ.restrict S0) X obs 0 =
      SAP.P001b.W1ArmMean μ X Y0 Y1 D 0 := by
    funext x
    let C : Set Ω := {ω | X ω = x}
    let J : Set Ω := {ω | X ω = x ∧ D ω = 0}
    have hC : MeasurableSet C := hX (measurableSet_singleton x)
    have hset : C ∩ S0 = J := by
      ext ω
      simp [C, J, S0]
    have hm : SAP.P001b.probability (μ.restrict S0) C = SAP.P001b.probability μ J := by
      simp [SAP.P001b.probability, Measure.restrict_apply hC, hset]
    have hi : (∫ ω in C, obs ω ∂(μ.restrict S0)) = (∫ ω in J, obs ω ∂μ) := by
      change (∫ ω, obs ω ∂((μ.restrict S0).restrict C)) = _
      rw [Measure.restrict_restrict hC, hset]
    simp [SAP.P001b.WH.W1.P.T22_L1V2.cellMean,
      SAP.P001b.W1ArmMean, C, J, hm, hi, obs]
  have hmean1 : SAP.P001b.WH.W1.P.T22_L1V2.cellMean (μ.restrict S1) X obs 0 =
      SAP.P001b.W1ArmMean μ X Y0 Y1 D 1 := by
    funext x
    let C : Set Ω := {ω | X ω = x}
    let J : Set Ω := {ω | X ω = x ∧ D ω = 1}
    have hC : MeasurableSet C := hX (measurableSet_singleton x)
    have hset : C ∩ S1 = J := by
      ext ω
      simp [C, J, S1]
    have hm : SAP.P001b.probability (μ.restrict S1) C = SAP.P001b.probability μ J := by
      simp [SAP.P001b.probability, Measure.restrict_apply hC, hset]
    have hi : (∫ ω in C, obs ω ∂(μ.restrict S1)) = (∫ ω in J, obs ω ∂μ) := by
      change (∫ ω, obs ω ∂((μ.restrict S1).restrict C)) = _
      rw [Measure.restrict_restrict hC, hset]
    simp [SAP.P001b.WH.W1.P.T22_L1V2.cellMean,
      SAP.P001b.W1ArmMean, C, J, hm, hi, obs]
  refine ⟨hpCEF, ?_, ?_⟩
  · simpa [hmean0, obs] using harm0
  · simpa [hmean1, obs] using harm1
