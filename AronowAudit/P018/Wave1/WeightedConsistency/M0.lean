import AronowAudit.P018.Wave1.WeightedConsistencyBlueprint

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

theorem firstUnit_ne_secondUnit {N : ℕ} (d : Dyad N) : firstUnit d ≠ secondUnit d := by
  exact ne_of_lt ((members d).min'_lt_max'_of_card (by rw [members_card]; omega))

theorem firstUnit_mem {N : ℕ} (d : Dyad N) : firstUnit d ∈ members d :=
  Finset.min'_mem _ _

theorem secondUnit_mem {N : ℕ} (d : Dyad N) : secondUnit d ∈ members d :=
  Finset.max'_mem _ _

theorem repeatedLaw_probability {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (N : ℕ) :
    IsProbabilityMeasure (repeatedLaw R N) := by
  letI instUnitProbability : IsProbabilityMeasure R.μ := hR.1
  unfold repeatedLaw
  infer_instance

theorem m0_proof : M0.{u} := by
  intro g1 U _ k R hR
  letI instUnitProbability : IsProbabilityMeasure R.μ := hR.1
  constructor
  · intro N d t
    have hp : Measurable (fun ω : Fin N → U => (ω (firstUnit d), ω (secondUnit d))) :=
      (measurable_pi_apply (firstUnit d)).prodMk (measurable_pi_apply (secondUnit d))
    constructor
    · simpa only [Function.comp_def, repeatedX] using (hR.2.2.1 N d t).1.comp hp
    · simpa only [Function.comp_def, repeatedY] using (hR.2.2.1 N d t).2.comp hp
  · obtain ⟨B, hB, hb⟩ := hR.2.2.2.1
    refine ⟨B, hB, ?_⟩
    intro N d t
    have h := hb N d t
    rw [← g1 R.μ (firstUnit d) (secondUnit d) (firstUnit_ne_secondUnit d)] at h
    exact ae_of_ae_map
      ((measurable_pi_apply (firstUnit d)).prodMk
        (measurable_pi_apply (secondUnit d))).aemeasurable h

end
end AronowAudit.P018.Wave1.WeightedConsistency
