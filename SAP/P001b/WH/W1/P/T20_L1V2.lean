import SAP.P001b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b.WH.W1.P.T20_L1V2

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Classical Topology

noncomputable section

lemma probability_eq_zero_iff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω) : SAP.P001b.probability μ A = 0 ↔ μ A = 0 := by
  simp [SAP.P001b.probability, ENNReal.toReal_eq_zero_iff, measure_ne_top]

lemma arm_law_absolutelyContinuous_marginal
    {Ω : Type*} {E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (D : Ω → ℝ) (hX : Measurable X) (d : ℝ) :
    SAP.P001b.W1ArmLaw μ X D d ≪ μ.map X := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hzero
  let T : Set Ω := X ⁻¹' A
  let S : Set Ω := {ω | D ω = d}
  have hTzero : μ T = 0 := by
    have hh := hzero
    rw [Measure.map_apply hX hA] at hh
    exact hh
  have hevent : μ (T ∩ S) = 0 :=
    measure_mono_null Set.inter_subset_left hTzero
  have hset : T ∩ S = {ω | X ω ∈ A ∧ D ω = d} := by
    ext ω
    simp [T, S]
  change ((μ S)⁻¹ • ((μ.restrict S).map X)) A = 0
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hX hA,
    Measure.restrict_apply (hX hA)]
  change (μ S)⁻¹ * μ (T ∩ S) = 0
  rw [hevent]
  simp

lemma marginal_absolutelyContinuous_arm_law
    {Ω : Type*} {E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ)
    (hX : Measurable X) (d ε : ℝ) (hε : 0 < ε)
    (hlower : ∀ A : Set E, MeasurableSet A →
      ε * SAP.P001b.probability μ (X ⁻¹' A) ≤
        SAP.P001b.probability μ {ω | X ω ∈ A ∧ D ω = d})
    (hArm : 0 < SAP.P001b.probability μ {ω | D ω = d}) :
    μ.map X ≪ SAP.P001b.W1ArmLaw μ X D d := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hzero
  let T : Set Ω := X ⁻¹' A
  let S : Set Ω := {ω | D ω = d}
  have hcoef : (μ S)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (measure_ne_top μ S)
  have hscaled : (μ S)⁻¹ * ((μ.restrict S).map X A) = 0 := by
    change ((μ S)⁻¹ • ((μ.restrict S).map X)) A = 0 at hzero
    simpa only [Measure.smul_apply, smul_eq_mul] using hzero
  have hraw : ((μ.restrict S).map X) A = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left hcoef
  have hset : T ∩ S = {ω | X ω ∈ A ∧ D ω = d} := by
    ext ω
    simp [T, S]
  have hevent : μ {ω | X ω ∈ A ∧ D ω = d} = 0 := by
    rw [Measure.map_apply hX hA, Measure.restrict_apply (hX hA)] at hraw
    change μ (T ∩ S) = 0 at hraw
    rw [hset] at hraw
    exact hraw
  have hprobEvent : SAP.P001b.probability μ {ω | X ω ∈ A ∧ D ω = d} = 0 :=
    (probability_eq_zero_iff μ _).2 hevent
  have hmul : ε * SAP.P001b.probability μ (X ⁻¹' A) ≤ 0 := by
    simpa [hprobEvent] using hlower A hA
  have hprobT : SAP.P001b.probability μ (X ⁻¹' A) = 0 := by
    have hnonneg : 0 ≤ SAP.P001b.probability μ (X ⁻¹' A) := ENNReal.toReal_nonneg
    nlinarith
  rw [Measure.map_apply hX hA]
  exact (probability_eq_zero_iff μ _).mp hprobT

lemma setIntegral_treated_eq_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℝ) (hD : Measurable D) (hbin : ∀ ω, D ω = 0 ∨ D ω = 1)
    (T : Set Ω) (hT : MeasurableSet T) :
    (∫ ω in T, D ω ∂μ) = SAP.P001b.probability μ {ω | ω ∈ T ∧ D ω = 1} := by
  let S : Set Ω := {ω | D ω = 1}
  have hS : MeasurableSet S := hD (measurableSet_singleton 1)
  have hfun : T.indicator D = (T ∩ S).indicator (fun _ : Ω => (1 : ℝ)) := by
    funext ω
    by_cases ht : ω ∈ T
    · simp only [Set.indicator_of_mem ht]
      by_cases hd : D ω = 1
      · simp [S, ht, hd]
      · have hd0 : D ω = 0 := (hbin ω).resolve_right hd
        simp [S, ht, hd, hd0]
    · simp [ht]
  rw [← integral_indicator hT, hfun]
  calc
    (∫ ω, (T ∩ S).indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ) = μ.real (T ∩ S) :=
      integral_indicator_one (hT.inter hS)
    _ = SAP.P001b.probability μ {ω | ω ∈ T ∧ D ω = 1} := by
      change (μ (T ∩ S)).toReal = (μ {ω | ω ∈ T ∧ D ω = 1}).toReal
      congr 1

lemma setIntegral_control_eq_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℝ) (hD : Measurable D) (hbin : ∀ ω, D ω = 0 ∨ D ω = 1)
    (T : Set Ω) (hT : MeasurableSet T) :
    (∫ ω in T, (1 - D ω) ∂μ) = SAP.P001b.probability μ {ω | ω ∈ T ∧ D ω = 0} := by
  let S : Set Ω := {ω | D ω = 0}
  have hS : MeasurableSet S := hD (measurableSet_singleton 0)
  have hfun : T.indicator (fun ω => 1 - D ω) =
      (T ∩ S).indicator (fun _ : Ω => (1 : ℝ)) := by
    funext ω
    by_cases ht : ω ∈ T
    · simp only [Set.indicator_of_mem ht]
      by_cases hd : D ω = 0
      · simp [S, ht, hd]
      · have hd1 : D ω = 1 := (hbin ω).resolve_left hd
        simp [S, ht, hd, hd1]
    · simp [ht]
  rw [← integral_indicator hT, hfun]
  calc
    (∫ ω, (T ∩ S).indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ) = μ.real (T ∩ S) :=
      integral_indicator_one (hT.inter hS)
    _ = SAP.P001b.probability μ {ω | ω ∈ T ∧ D ω = 0} := by
      change (μ (T ∩ S)).toReal = (μ {ω | ω ∈ T ∧ D ω = 0}).toReal
      congr 1

lemma propensity_region_bounds
    {Ω : Type*} {E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ)
    (hX : Measurable X) (hD : Measurable D)
    (hbin : ∀ ω, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : SAP.P001b.W1CEF μ X D p)
    {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε < p (X ω) ∧ p (X ω) < 1 - ε)
    (A : Set E) (hA : MeasurableSet A) :
    ε * SAP.P001b.probability μ (X ⁻¹' A) ≤
        SAP.P001b.probability μ {ω | X ω ∈ A ∧ D ω = 1} ∧
      SAP.P001b.probability μ {ω | X ω ∈ A ∧ D ω = 1} ≤
        (1 - ε) * SAP.P001b.probability μ (X ⁻¹' A) ∧
      ε * SAP.P001b.probability μ (X ⁻¹' A) ≤
        SAP.P001b.probability μ {ω | X ω ∈ A ∧ D ω = 0} ∧
      SAP.P001b.probability μ {ω | X ω ∈ A ∧ D ω = 0} ≤
        (1 - ε) * SAP.P001b.probability μ (X ⁻¹' A) := by
  let T : Set Ω := X ⁻¹' A
  have hT : MeasurableSet T := hX hA
  have hpX : Integrable (fun ω => p (X ω)) μ := hp.2.2.1
  have hcef := hp.2.2.2 A hA
  have hpInt : Integrable (fun ω => p (X ω)) (μ.restrict T) :=
    hpX.mono_measure Measure.restrict_le_self
  have hctrlInt : Integrable (fun ω => 1 - p (X ω)) (μ.restrict T) :=
    (integrable_const (1 : ℝ)).sub hpInt
  have hlowPae : ∀ᵐ ω ∂μ.restrict T, ε ≤ p (X ω) := by
    filter_upwards [ae_restrict_of_ae (hpos.mono fun ω hω => le_of_lt hω.1)] with ω hω
    exact hω
  have huppPae : ∀ᵐ ω ∂μ.restrict T, p (X ω) ≤ 1 - ε := by
    filter_upwards [ae_restrict_of_ae (hpos.mono fun ω hω => le_of_lt hω.2)] with ω hω
    exact hω
  have hlowCtrlPae : ∀ᵐ ω ∂μ.restrict T, ε ≤ 1 - p (X ω) := by
    filter_upwards [hpos.filter_mono (Measure.ae_mono' Measure.absolutelyContinuous_restrict)] with ω hω
    linarith [hω.1]
  have huppCtrlPae : ∀ᵐ ω ∂μ.restrict T, 1 - p (X ω) ≤ 1 - ε := by
    filter_upwards [hpos.filter_mono (Measure.ae_mono' Measure.absolutelyContinuous_restrict)] with ω hω
    linarith [hω.2]
  have hlowP := integral_mono_ae (integrable_const ε) hpInt hlowPae
  have huppP := integral_mono_ae hpInt (integrable_const (1 - ε)) huppPae
  have hlowCtrl := integral_mono_ae (integrable_const ε) hctrlInt hlowCtrlPae
  have huppCtrl := integral_mono_ae hctrlInt (integrable_const (1 - ε)) huppCtrlPae
  have hconstant (c : ℝ) :
      (∫ _ : Ω, c ∂μ.restrict T) = c * SAP.P001b.probability μ T := by
    simp [probability, Measure.real_def, Measure.restrict_apply_univ, mul_comm]
  have htreated := setIntegral_treated_eq_probability μ D hD hbin T hT
  have hcontrol := setIntegral_control_eq_probability μ D hD hbin T hT
  have htreatedId : (∫ ω in T, D ω ∂μ) = ∫ ω in T, p (X ω) ∂μ := hcef
  have hcontrolId : (∫ ω in T, (1 - D ω) ∂μ) = ∫ ω in T, (1 - p (X ω)) ∂μ := by
    change (∫ ω, (1 - D ω) ∂μ.restrict T) =
      (∫ ω, (1 - p (X ω)) ∂μ.restrict T)
    rw [integral_sub (integrable_const (1 : ℝ))
          ((hp.2.1).mono_measure Measure.restrict_le_self),
        integral_sub (integrable_const (1 : ℝ)) hpInt, htreatedId]
  have hTprob : SAP.P001b.probability μ T = SAP.P001b.probability μ (X ⁻¹' A) := by
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      ε * SAP.P001b.probability μ (X ⁻¹' A) =
          ∫ _ : Ω, ε ∂μ.restrict T := by rw [hconstant, hTprob]
      _ ≤ ∫ ω in T, p (X ω) ∂μ := hlowP
      _ = SAP.P001b.probability μ {ω | X ω ∈ A ∧ D ω = 1} := by
        rw [← htreatedId, htreated]
        rfl
  · calc
      SAP.P001b.probability μ {ω | X ω ∈ A ∧ D ω = 1} =
          ∫ ω in T, p (X ω) ∂μ := by
        change SAP.P001b.probability μ {ω | ω ∈ T ∧ D ω = 1} = _
        exact htreated.symm.trans htreatedId
      _ ≤ ∫ _ : Ω, (1 - ε) ∂μ.restrict T := huppP
      _ = (1 - ε) * SAP.P001b.probability μ (X ⁻¹' A) := by rw [hconstant, hTprob]
  · calc
      ε * SAP.P001b.probability μ (X ⁻¹' A) =
          ∫ _ : Ω, ε ∂μ.restrict T := by rw [hconstant, hTprob]
      _ ≤ ∫ ω in T, (1 - p (X ω)) ∂μ := hlowCtrl
      _ = SAP.P001b.probability μ {ω | X ω ∈ A ∧ D ω = 0} := by
        rw [← hcontrolId, hcontrol]
        rfl
  · calc
      SAP.P001b.probability μ {ω | X ω ∈ A ∧ D ω = 0} =
          ∫ ω in T, (1 - p (X ω)) ∂μ := by
        change SAP.P001b.probability μ {ω | ω ∈ T ∧ D ω = 0} = _
        exact hcontrol.symm.trans hcontrolId
      _ ≤ ∫ _ : Ω, (1 - ε) ∂μ.restrict T := huppCtrl
      _ = (1 - ε) * SAP.P001b.probability μ (X ⁻¹' A) := by rw [hconstant, hTprob]

end

end SAP.P001b.WH.W1.P.T20_L1V2

theorem SAP.P001b.WH.W1.T20_L1V2_proof : SAP.P001b.WH.W1.T20_L1V2 := by
  intro Ω E instΩ instE μ hμ X D hX hD hbin hD0 hD1 p hp hpos
  rcases hpos with ⟨ε, hε, hpos⟩
  have hlower1 : ∀ A : Set E, MeasurableSet A →
      ε * SAP.P001b.probability μ (X ⁻¹' A) ≤
        SAP.P001b.probability μ {ω | X ω ∈ A ∧ D ω = 1} := by
    intro A hA
    exact (SAP.P001b.WH.W1.P.T20_L1V2.propensity_region_bounds
      μ X D hX hD hbin p hp hε hpos A hA).1
  have hlower0 : ∀ A : Set E, MeasurableSet A →
      ε * SAP.P001b.probability μ (X ⁻¹' A) ≤
        SAP.P001b.probability μ {ω | X ω ∈ A ∧ D ω = 0} := by
    intro A hA
    exact (SAP.P001b.WH.W1.P.T20_L1V2.propensity_region_bounds
      μ X D hX hD hbin p hp hε hpos A hA).2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact SAP.P001b.WH.W1.P.T20_L1V2.arm_law_absolutelyContinuous_marginal
      μ X D hX 1
  · exact SAP.P001b.WH.W1.P.T20_L1V2.marginal_absolutelyContinuous_arm_law
      μ X D hX 1 ε hε hlower1 hD1
  · exact SAP.P001b.WH.W1.P.T20_L1V2.arm_law_absolutelyContinuous_marginal
      μ X D hX 0
  · exact SAP.P001b.WH.W1.P.T20_L1V2.marginal_absolutelyContinuous_arm_law
      μ X D hX 0 ε hε hlower0 hD0
