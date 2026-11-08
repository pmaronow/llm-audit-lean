import SAP.P029b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W1.P.T16_L2

universe u v

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

lemma finite_profile_integrable {Ω : Type u} {X : Type v}
    [MeasurableSpace Ω] [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω → X) (hT : Measurable T) (f : X → ℝ) :
    Integrable (fun ω => f (T ω)) μ := by
  have hm : Measurable (fun ω => f (T ω)) := (measurable_of_finite f).comp hT
  apply Integrable.of_bound hm.aestronglyMeasurable (∑ x : X, ‖f x‖)
  filter_upwards with ω
  have hle : ‖f (T ω)‖ ≤ ∑ x : X, ‖f x‖ := by
    exact Finset.single_le_sum (fun x hx => norm_nonneg (f x)) (Finset.mem_univ (T ω))
  exact hle

lemma profile_score_mass {Ω : Type u} {X : Type v} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (x : X) :
    mP μ {ω | (U ω).x = x} * scoreAt μ U x =
      mP μ {ω | (U ω).complier ∧ (U ω).x = x} := by
  let A : Set Ω := {ω | (U ω).x = x}
  let C : Set Ω := {ω | (U ω).complier ∧ (U ω).x = x}
  have hle : mP μ C ≤ mP μ A := by
    apply ENNReal.toReal_mono (measure_ne_top μ A)
    exact measure_mono (by
      intro ω hω
      exact hω.2)
  by_cases hA : mP μ A = 0
  · have hC : mP μ C = 0 := le_antisymm (by simpa [hA] using hle)
      (ENNReal.toReal_nonneg)
    simp [scoreAt, A, C, hA, hC]
  · rw [scoreAt]
    change mP μ A * (mP μ C / mP μ A) = mP μ C
    exact mul_div_cancel₀ _ hA

lemma profile_product_mass_integral {Ω : Type u} {X : Type v}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (x : X) :
    mP μ {ω | (U ω).x = x} * scoreAt μ U x * complierAt μ U x =
      ∫ ω in {ω | (U ω).complier ∧ (U ω).x = x}, (U ω).tau ∂μ := by
  rw [profile_score_mass]
  exact AronowAudit.P029.Wave1.wcl_mass_mul_mean
    (fun ω => (U ω).tau) {ω | (U ω).complier ∧ (U ω).x = x}

lemma setIntegral_eq_of_profile_cells {Ω : Type u} {X : Type v}
    [MeasurableSpace Ω] [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] {μ : Measure Ω}
    (T : Ω → X) (hT : Measurable T) {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hcell : ∀ x, (∫ ω in {ω | T ω = x}, g ω ∂μ) =
      ∫ ω in {ω | T ω = x}, f ω ∂μ)
    (s : Set Ω) (hs : MeasurableSet[MeasurableSpace.comap T inferInstance] s) :
    (∫ ω in s, g ω ∂μ) = ∫ ω in s, f ω ∂μ := by
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hA : MeasurableSet (T ⁻¹' B) := hT hB
  have hrepr (v : Ω → ℝ) (hv : Integrable v μ) :
      (∫ ω in T ⁻¹' B, v ω ∂μ) =
        ∑ x : X, (if x ∈ B then (1 : ℝ) else 0) *
          (∫ ω in {ω | T ω = x}, v ω ∂μ) := by
    rw [← integral_indicator hA]
    simpa [Set.indicator_apply] using
      (AronowAudit.P029.Wave1.wcl_profile_integral hT hv
        (fun x => if x ∈ B then (1 : ℝ) else 0))
  calc
    _ = ∑ x : X, (if x ∈ B then (1 : ℝ) else 0) *
        (∫ ω in {ω | T ω = x}, g ω ∂μ) := hrepr g hg
    _ = ∑ x : X, (if x ∈ B then (1 : ℝ) else 0) *
        (∫ ω in {ω | T ω = x}, f ω ∂μ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hcell x]
    _ = _ := (hrepr f hf).symm

theorem canonical_score_versions {Ω : Type u} {X : Type v}
    [MeasurableSpace Ω] [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z) :
    ScoreVersions μ U (scoreAt μ U) (complierAt μ U) := by
  let T : Ω → X := fun ω => (U ω).x
  have hT : Measurable T := hiv.1
  let V : Ω → AronowAudit.P029.PotentialUnit X :=
    fun ω => SAP.P029b.Bridge.toUnit (U ω)
  have hiv' : AronowAudit.P029.IVAssumptions μ V Z := by
    change AronowAudit.P029.IVAssumptions μ
      (fun ω => SAP.P029b.Bridge.toUnit (U ω)) Z
    exact (SAP.P029b.Bridge.iv_eq μ U Z).symm ▸ hiv
  have hC : MeasurableSet {ω | (U ω).complier} :=
    by
      simpa [V, SAP.P029b.Bridge.toUnit,
        SAP.P029b.PotentialUnit.complier, AronowAudit.P029.PotentialUnit.complier] using
        (AronowAudit.P029.Wave1.GP029B3b_appendix_complier_measurable
          (μ := μ) (U := V) (Z := Z) hiv')
  have hfi : Integrable (fun ω => if (U ω).complier then (1 : ℝ) else 0) μ :=
    by
      convert (AronowAudit.P029.Wave1.GP029B3b_appendix_indicator_integrable
          (μ := μ) (U := V) (Z := Z) hiv') using 1 <;>
        ext ω <;> simp [V, SAP.P029b.Bridge.toUnit,
          SAP.P029b.PotentialUnit.complier, AronowAudit.P029.PotentialUnit.complier] <;> rfl
  have hgi : Integrable (fun ω => scoreAt μ U ((U ω).x)) μ :=
    finite_profile_integrable T hT (scoreAt μ U)
  have hcellScore (x : X) :
      (∫ ω in {ω | (U ω).x = x}, scoreAt μ U ((U ω).x) ∂μ) =
        ∫ ω in {ω | (U ω).x = x},
          (if (U ω).complier then (1 : ℝ) else 0) ∂μ := by
    have hleft := AronowAudit.P029.Wave1.wcl_cell_integral (μ := μ) hT (scoreAt μ U) x
    have hright := AronowAudit.P029.Wave1.wcl_event_cell_integral
      (μ := μ) hT hC (fun _ => (1 : ℝ)) x
    calc
      _ = mP μ {ω | (U ω).x = x} * scoreAt μ U x := hleft
      _ = mP μ {ω | (U ω).complier ∧ (U ω).x = x} := profile_score_mass U x
      _ = ∫ ω in {ω | (U ω).complier ∧ (U ω).x = x}, (1 : ℝ) ∂μ := by
        simp [mP, measureReal_def]
      _ = _ := by simpa [Set.mem_setOf_eq] using hright.symm
  have hscoreSubMeas :
      AEStronglyMeasurable[ covariateSigma U]
        (fun ω => scoreAt μ U ((U ω).x)) μ := by
    have hX : Measurable[covariateSigma U] T := by
      intro s hs
      exact ⟨s, hs, rfl⟩
    exact ((measurable_of_finite (scoreAt μ U)).comp hX).aestronglyMeasurable
  have hscoreCE :
      (fun ω => scoreAt μ U ((U ω).x)) =ᵐ[μ]
        condExp (covariateSigma U) μ
          (fun ω => if (U ω).complier then (1 : ℝ) else 0) := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hiv.1.comap_le hfi
    · intro s hs hfinite
      exact hgi.integrableOn
    · intro s hs hfinite
      exact setIntegral_eq_of_profile_cells T hT hfi hgi hcellScore s hs
    · exact hscoreSubMeas
  have hprod : Integrable
      (fun ω => scoreAt μ U ((U ω).x) * complierAt μ U ((U ω).x)) μ :=
    finite_profile_integrable T hT (fun x => scoreAt μ U x * complierAt μ U x)
  have hti : Integrable
      (fun ω => if (U ω).complier then (U ω).tau else 0) μ :=
    by
      convert (AronowAudit.P029.Wave1.GP029B3b_appendix_effect_integrable
          (μ := μ) (U := V) (Z := Z) hiv') using 1 <;>
        ext ω <;> simp [V, SAP.P029b.Bridge.toUnit,
          SAP.P029b.PotentialUnit.complier, AronowAudit.P029.PotentialUnit.complier,
          SAP.P029b.PotentialUnit.tau, AronowAudit.P029.PotentialUnit.tau] <;> rfl
  have hcellProd (x : X) :
      (∫ ω in {ω | (U ω).x = x},
        scoreAt μ U ((U ω).x) * complierAt μ U ((U ω).x) ∂μ) =
        ∫ ω in {ω | (U ω).x = x},
          (if (U ω).complier then (U ω).tau else 0) ∂μ := by
    have hleft := AronowAudit.P029.Wave1.wcl_cell_integral (μ := μ) hT
      (fun x => scoreAt μ U x * complierAt μ U x) x
    have hright := AronowAudit.P029.Wave1.wcl_event_cell_integral
      (μ := μ) hT hC (fun ω => (U ω).tau) x
    calc
      _ = mP μ {ω | (U ω).x = x} * scoreAt μ U x * complierAt μ U x := by
        simpa [T, mul_assoc, SAP.P029b.mP, AronowAudit.P029.mP] using hleft
      _ = ∫ ω in {ω | (U ω).complier ∧ (U ω).x = x}, (U ω).tau ∂μ :=
        profile_product_mass_integral U x
      _ = _ := by simpa [Set.mem_setOf_eq] using hright.symm
  have hprodSubMeas :
      AEStronglyMeasurable[ covariateSigma U]
        (fun ω => scoreAt μ U ((U ω).x) * complierAt μ U ((U ω).x)) μ := by
    have hX : Measurable[covariateSigma U] T := by
      intro s hs
      exact ⟨s, hs, rfl⟩
    exact ((measurable_of_finite
      (fun x => scoreAt μ U x * complierAt μ U x)).comp hX).aestronglyMeasurable
  have hprodCE :
      (fun ω => scoreAt μ U ((U ω).x) * complierAt μ U ((U ω).x)) =ᵐ[μ]
        condExp (covariateSigma U) μ
          (fun ω => if (U ω).complier then (U ω).tau else 0) := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hiv.1.comap_le hti
    · intro s hs hfinite
      exact hprod.integrableOn
    · intro s hs hfinite
      exact setIntegral_eq_of_profile_cells T hT hti hprod hcellProd s hs
    · exact hprodSubMeas
  exact ⟨measurable_of_finite _, measurable_of_finite _, hscoreCE, hprodCE⟩

end
end SAP.P029b.WH.W1.P.T16_L2

theorem SAP.P029b.WH.W1.T16_L2_proof : SAP.P029b.WH.W1.T16_L2 := by
  intro Ω X instΩ instX fintypeX measX μ hμ U Z hiv
  exact SAP.P029b.WH.W1.P.T16_L2.canonical_score_versions μ U Z hiv
