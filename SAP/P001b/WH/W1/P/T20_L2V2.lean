import SAP.P001b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b.WH.W1.P.T20_L2V2

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Classical Topology

noncomputable section

lemma setIntegral_binary_eq_probability
    {Ω : Type*} {E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → E) (D : Ω → ℝ) (A : Set E)
    (hX : Measurable X) (hD : Measurable D)
    (hbin : ∀ ω, D ω = 0 ∨ D ω = 1) (hA : MeasurableSet A) :
    (∫ ω in X ⁻¹' A, D ω ∂μ) =
      probability μ {ω | X ω ∈ A ∧ D ω = 1} := by
  let T : Set Ω := {ω | X ω ∈ A ∧ D ω = 1}
  have hpre : MeasurableSet (X ⁻¹' A) := hX hA
  have hT : MeasurableSet T := by
    change MeasurableSet {ω | X ω ∈ A ∧ D ω = 1}
    change MeasurableSet ((X ⁻¹' A) ∩ D ⁻¹' ({1} : Set ℝ))
    exact hpre.inter (hD (measurableSet_singleton 1))
  have hfun : (X ⁻¹' A).indicator D = T.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hx : X ω ∈ A
    · rcases hbin ω with hzero | hone
      · simp [T, Set.indicator, hx, hzero]
      · simp [T, Set.indicator, hx, hone]
    · simp [T, Set.indicator, hx]
  calc
    (∫ ω in X ⁻¹' A, D ω ∂μ) = ∫ ω, (X ⁻¹' A).indicator D ω ∂μ :=
      (integral_indicator hpre).symm
    _ = ∫ ω, T.indicator (fun _ => (1 : ℝ)) ω ∂μ := by rw [hfun]
    _ = μ.real T := integral_indicator_one hT
    _ = probability μ T := rfl

lemma region_probability_eq_arm_sum
    {Ω : Type*} {E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → E) (D : Ω → ℝ) (A : Set E)
    (hX : Measurable X) (hD : Measurable D)
    (hbin : ∀ ω, D ω = 0 ∨ D ω = 1) (hA : MeasurableSet A) :
    probability μ (X ⁻¹' A) =
      probability μ {ω | X ω ∈ A ∧ D ω = 1} +
        probability μ {ω | X ω ∈ A ∧ D ω = 0} := by
  let T : Set Ω := {ω | X ω ∈ A ∧ D ω = 1}
  let C : Set Ω := {ω | X ω ∈ A ∧ D ω = 0}
  have hpre : MeasurableSet (X ⁻¹' A) := hX hA
  have hT : MeasurableSet T := by
    change MeasurableSet {ω | X ω ∈ A ∧ D ω = 1}
    change MeasurableSet ((X ⁻¹' A) ∩ D ⁻¹' ({1} : Set ℝ))
    exact hpre.inter (hD (measurableSet_singleton 1))
  have hC : MeasurableSet C := by
    change MeasurableSet {ω | X ω ∈ A ∧ D ω = 0}
    change MeasurableSet ((X ⁻¹' A) ∩ D ⁻¹' ({0} : Set ℝ))
    exact hpre.inter (hD (measurableSet_singleton 0))
  have hdisj : Disjoint T C := by
    refine Set.disjoint_left.mpr ?_
    intro ω ht hc
    have ht' : D ω = 1 := ht.2
    have hc' : D ω = 0 := hc.2
    linarith
  have hunion : X ⁻¹' A = T ∪ C := by
    ext ω
    constructor
    · intro hx
      rcases hbin ω with hzero | hone
      · exact Or.inr ⟨hx, hzero⟩
      · exact Or.inl ⟨hx, hone⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
      · exact hx
      · exact hx
  change μ.real (X ⁻¹' A) = μ.real T + μ.real C
  rw [hunion, measureReal_union hdisj hC]

end

end SAP.P001b.WH.W1.P.T20_L2V2

open MeasureTheory ProbabilityTheory Filter

open SAP.P001b.WH.W1.P.T20_L2V2

theorem SAP.P001b.WH.W1.T20_L2V2_proof : SAP.P001b.WH.W1.T20_L2V2 := by
  intro Ω E instΩ instE μ hμ X D hX hD hbin p hcef A hA hmass
  letI : IsProbabilityMeasure μ := hμ
  rcases hcef with ⟨hpmeas, hDint, hpint, hcefSet⟩
  have hregion := region_probability_eq_arm_sum μ X D A hX hD hbin hA
  constructor
  · intro hzero
    have hpzero : (∫ ω in X ⁻¹' A, p (X ω) ∂μ) = 0 := by
      calc
        (∫ ω in X ⁻¹' A, p (X ω) ∂μ) =
            ∫ ω, p (X ω) ∂μ.restrict (X ⁻¹' A) := rfl
        _ = ∫ _ω, (0 : ℝ) ∂μ.restrict (X ⁻¹' A) := integral_congr_ae hzero
        _ = 0 := by simp
    have htreated : probability μ {ω | X ω ∈ A ∧ D ω = 1} = 0 := by
      calc
        probability μ {ω | X ω ∈ A ∧ D ω = 1} =
            ∫ ω in X ⁻¹' A, D ω ∂μ :=
              (setIntegral_binary_eq_probability μ X D A hX hD hbin hA).symm
        _ = ∫ ω in X ⁻¹' A, p (X ω) ∂μ := hcefSet A hA
        _ = 0 := hpzero
    have hmass' := hmass
    rw [hregion, htreated] at hmass'
    exact ⟨htreated, by linarith⟩
  · intro hone
    have hpone : (∫ ω in X ⁻¹' A, p (X ω) ∂μ) = probability μ (X ⁻¹' A) := by
      calc
        (∫ ω in X ⁻¹' A, p (X ω) ∂μ) =
            ∫ ω, p (X ω) ∂μ.restrict (X ⁻¹' A) := rfl
        _ = ∫ _ω, (1 : ℝ) ∂μ.restrict (X ⁻¹' A) := integral_congr_ae hone
        _ = probability μ (X ⁻¹' A) := by
          rw [setIntegral_const]
          simp only [smul_eq_mul, mul_one, probability, Measure.real]
    have htreated : probability μ {ω | X ω ∈ A ∧ D ω = 1} =
        probability μ (X ⁻¹' A) := by
      calc
        probability μ {ω | X ω ∈ A ∧ D ω = 1} =
            ∫ ω in X ⁻¹' A, D ω ∂μ :=
              (setIntegral_binary_eq_probability μ X D A hX hD hbin hA).symm
        _ = ∫ ω in X ⁻¹' A, p (X ω) ∂μ := hcefSet A hA
        _ = probability μ (X ⁻¹' A) := hpone
    have hreg' := hregion
    rw [htreated] at hreg'
    have hcontrol : probability μ {ω | X ω ∈ A ∧ D ω = 0} = 0 := by linarith
    exact ⟨hcontrol, by simpa [htreated] using hmass⟩
