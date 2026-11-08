import AronowAudit.P001.Wave1.VarianceSEContractBlueprint

/-! Node N1 (= Target) of the P001-T55 records 47–48 blueprint (trivial; written by the
blueprint architect): the proved frozen `sample_mean_variance_estimate_scale` and
`variance_se_consistency_equivalence` give all three equivalences. -/

namespace AronowAudit.P001.Wave1.VarianceSEContract

open AronowAudit.P001 MeasureTheory ProbabilityTheory

theorem n1_proof : N1 := by
  intro Ω _ μ _ θhat Vhat θ _ hV hVnn ν _ _ _
  have hscale := sample_mean_variance_estimate_scale μ Vhat hV (var ν id)
  exact ⟨hscale.1, hscale.2,
    variance_se_consistency_equivalence μ Vhat hVnn (var ν id) (variance_nonneg _ _)⟩

end AronowAudit.P001.Wave1.VarianceSEContract
