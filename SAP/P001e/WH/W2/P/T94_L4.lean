import SAP.P001e.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e.WH.W2.P.T94_L4
universe u v

theorem covariate_null_of_arm_null
    {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (D : Ω → ℝ) (hD : Measurable D) (hb : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : SAP.P001e.IsConditionalMean μ X D p)
    (hpos : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω) ∧ p (X ω) < 1 - ε)
    (A : Set E) (hA : MeasurableSet A) (d : ℝ) (hd : d = 0 ∨ d = 1)
    (hz : μ (X ⁻¹' A ∩ {ω | D ω = d}) = 0) : μ (X ⁻¹' A) = 0 := by
  obtain ⟨ε, hε, hεpos⟩ := hpos
  let B : Set Ω := X ⁻¹' A
  have hB : MeasurableSet B := hX hA
  have hT1 : MeasurableSet {ω | D ω = (1 : ℝ)} :=
    measurableSet_eq_fun hD measurable_const
  have hT0 : MeasurableSet {ω | D ω = (0 : ℝ)} :=
    measurableSet_eq_fun hD measurable_const
  have hD1 : (fun ω => D ω) =ᵐ[μ.restrict B]
      ({ω | D ω = (1 : ℝ)}.indicator (fun _ => (1 : ℝ))) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hB]
    filter_upwards [hb] with ω hω hωB
    rcases hω with hω | hω
    · simp [hω]
    · simp [hω]
  have hD0 : (fun ω => 1 - D ω) =ᵐ[μ.restrict B]
      ({ω | D ω = (0 : ℝ)}.indicator (fun _ => (1 : ℝ))) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hB]
    filter_upwards [hb] with ω hω hωB
    rcases hω with hω | hω
    · simp [hω]
    · simp [hω]
  have hArm1 : (∫ ω in B, D ω ∂μ) = (μ (B ∩ {ω | D ω = (1 : ℝ)})).toReal := by
    calc
      (∫ ω in B, D ω ∂μ) =
          ∫ ω in B, ({ω | D ω = (1 : ℝ)}.indicator (fun _ => (1 : ℝ))) ω ∂μ :=
        integral_congr_ae hD1
      _ = ∫ ω in B ∩ {ω | D ω = (1 : ℝ)}, (1 : ℝ) ∂μ := by
        rw [← integral_indicator hB, ← integral_indicator (hB.inter hT1)]
        congr 1
        funext ω
        by_cases hωB : ω ∈ B <;> by_cases hωT : D ω = 1 <;>
          simp [Set.indicator, hωB, hωT]
      _ = (μ (B ∩ {ω | D ω = (1 : ℝ)})).toReal := by
        simp [measureReal_def]
  have hArm0 : (∫ ω in B, 1 - D ω ∂μ) = (μ (B ∩ {ω | D ω = (0 : ℝ)})).toReal := by
    calc
      (∫ ω in B, 1 - D ω ∂μ) =
          ∫ ω in B, ({ω | D ω = (0 : ℝ)}.indicator (fun _ => (1 : ℝ))) ω ∂μ :=
        integral_congr_ae hD0
      _ = ∫ ω in B ∩ {ω | D ω = (0 : ℝ)}, (1 : ℝ) ∂μ := by
        rw [← integral_indicator hB, ← integral_indicator (hB.inter hT0)]
        congr 1
        funext ω
        by_cases hωB : ω ∈ B <;> by_cases hωT : D ω = 0 <;>
          simp [Set.indicator, hωB, hωT]
      _ = (μ (B ∩ {ω | D ω = (0 : ℝ)})).toReal := by
        simp [measureReal_def]
  have hpLower :
      (∫ ω in B, (fun _ : Ω => ε) ω ∂μ) ≤ ∫ ω in B, p (X ω) ∂μ := by
    apply setIntegral_mono_ae_restrict
      (integrableOn_const (measure_ne_top μ B))
      hp.2.2.1.integrableOn
    rw [EventuallyLE, ae_restrict_iff' hB]
    filter_upwards [hεpos] with ω hω hωB
    exact le_of_lt hω.1
  have hpLower' : ε * (μ B).toReal ≤ ∫ ω in B, p (X ω) ∂μ := by
    simpa [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm] using hpLower
  have hconstInt : IntegrableOn (fun _ : Ω => (1 : ℝ)) B μ :=
    integrableOn_const (measure_ne_top μ B)
  have hpInt : IntegrableOn (fun ω => p (X ω)) B μ := hp.2.2.1.integrableOn
  have hpCompInt : IntegrableOn (fun ω => 1 - p (X ω)) B μ := hconstInt.sub hpInt
  have hpCompLower :
      (∫ ω in B, (fun _ : Ω => ε) ω ∂μ) ≤ ∫ ω in B, 1 - p (X ω) ∂μ := by
    apply setIntegral_mono_ae_restrict (integrableOn_const (measure_ne_top μ B)) hpCompInt
    rw [EventuallyLE, ae_restrict_iff' hB]
    filter_upwards [hεpos] with ω hω hωB
    exact le_of_lt (by linarith [hω.2])
  have hpCompLower' : ε * (μ B).toReal ≤ ∫ ω in B, 1 - p (X ω) ∂μ := by
    simpa [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm] using hpCompLower
  have hzeroReal : (μ B).toReal = 0 := by
    rcases hd with hd0 | hd1
    · subst d
      have hzreal : (μ (B ∩ {ω | D ω = (0 : ℝ)})).toReal = 0 := by
        simpa [B] using congrArg ENNReal.toReal hz
      have hcef := hp.2.2.2 A hA
      have hsub : (∫ ω in B, 1 - D ω ∂μ) = ∫ ω in B, 1 - p (X ω) ∂μ := by
        rw [integral_sub hconstInt hp.2.1.integrableOn, integral_sub hconstInt hpInt, hcef]
      have hcompl : ∫ ω in B, 1 - p (X ω) ∂μ = 0 := by
        calc
          (∫ ω in B, 1 - p (X ω) ∂μ) = ∫ ω in B, 1 - D ω ∂μ := hsub.symm
          _ = (μ (B ∩ {ω | D ω = (0 : ℝ)})).toReal := hArm0
          _ = 0 := hzreal
      have hbound := hpCompLower'
      rw [hcompl] at hbound
      have hεmul : ε * (μ B).toReal ≤ 0 := hbound
      have hμnonneg : 0 ≤ (μ B).toReal := ENNReal.toReal_nonneg
      nlinarith
    · subst d
      have hzreal : (μ (B ∩ {ω | D ω = (1 : ℝ)})).toReal = 0 := by
        simpa [B] using congrArg ENNReal.toReal hz
      have hcef := hp.2.2.2 A hA
      have hpZero : ∫ ω in B, p (X ω) ∂μ = 0 := by
        calc
          (∫ ω in B, p (X ω) ∂μ) = ∫ ω in B, D ω ∂μ := hcef.symm
          _ = (μ (B ∩ {ω | D ω = (1 : ℝ)})).toReal := hArm1
          _ = 0 := hzreal
      have hbound := hpLower'
      rw [hpZero] at hbound
      have hεmul : ε * (μ B).toReal ≤ 0 := hbound
      have hμnonneg : 0 ≤ (μ B).toReal := ENNReal.toReal_nonneg
      nlinarith
  have hμB : μ B = 0 := by
    by_contra hne
    have hposReal : 0 < (μ B).toReal := ENNReal.toReal_pos hne (measure_ne_top μ B)
    linarith
  exact hμB

end SAP.P001e.WH.W2.P.T94_L4

theorem SAP.P001e.WH.W2.T94_L4_proof : SAP.P001e.WH.W2.T94_L4 := by
  intro Ω E _ _ μ hμ X hX D hD hb p hp hpos F G hF hG he d hd
  let A : Set E := {x | F (d, x) ≠ G (d, x)}
  have hFd : Measurable (fun x => F (d, x)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  have hGd : Measurable (fun x => G (d, x)) :=
    hG.comp (measurable_const.prodMk measurable_id)
  have hA : MeasurableSet A := by
    exact (measurableSet_eq_fun hFd hGd).compl
  have hJoint : Measurable (fun ω => (D ω, X ω)) := hD.prodMk hX
  have hEqSet : MeasurableSet {z : ℝ × E | F z = G z} := measurableSet_eq_fun hF hG
  have heω : ∀ᵐ ω ∂μ, F (D ω, X ω) = G (D ω, X ω) :=
    (ae_map_iff hJoint.aemeasurable hEqSet).mp he
  have hMismatch : μ {ω | F (D ω, X ω) ≠ G (D ω, X ω)} = 0 := by
    have h := (ae_iff).mp heω
    simpa [ne_eq] using h
  have hz : μ (X ⁻¹' A ∩ {ω | D ω = d}) = 0 := by
    apply le_antisymm ?_ bot_le
    calc
      μ (X ⁻¹' A ∩ {ω | D ω = d}) ≤
          μ {ω | F (D ω, X ω) ≠ G (D ω, X ω)} := by
            apply measure_mono
            intro ω hω
            rcases hω with ⟨hωA, hωd⟩
            change F (d, X ω) ≠ G (d, X ω) at hωA
            change F (D ω, X ω) ≠ G (D ω, X ω)
            rw [hωd]
            exact hωA
      _ = 0 := hMismatch
  have hcov := SAP.P001e.WH.W2.P.T94_L4.covariate_null_of_arm_null
    μ X hX D hD hb p hp hpos A hA d hd hz
  change ∀ᵐ x ∂μ.map X, F (d, x) = G (d, x)
  rw [ae_iff, Measure.map_apply hX hA]
  simpa [A, ne_eq] using hcov
