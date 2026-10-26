import AronowAudit.P001.Wave1.VarianceSEContractBlueprint

/-! P001-T55: variance and standard-error consistency. The identities `sample_mean_variance_estimate_scale` and
`variance_se_consistency_equivalence` give all three equivalences. -/

namespace AronowAudit.P001.Wave1.VarianceSEContract

open AronowAudit.P001 MeasureTheory ProbabilityTheory

theorem n1_proof : N1 := by
  intro Ω _ μ _ θhat Vhat θ _ hV hVnn ν _ _ _
  have hscale := sample_mean_variance_estimate_scale μ Vhat hV (var ν id)
  exact ⟨hscale.1, hscale.2,
    variance_se_consistency_equivalence μ Vhat hVnn (var ν id) (variance_nonneg _ _)⟩

end AronowAudit.P001.Wave1.VarianceSEContract
