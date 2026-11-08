import AronowAudit.P027.Wave1.CancellationModelBlueprint
import AronowAudit.P027.Wave1.GaussianMoments
import AronowAudit.P027.Wave1.CancellationModel.N2

namespace AronowAudit.P027.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable

theorem cancellation_model_counterexample :
    ¬ (∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (r m : ℕ) (hr : 0 < r), 0 < m →
        r = 2 ∨ r = 10 → m = 2 ∨ m = 30 ∨ m = 60 →
        ∀ (ρ β : ℝ), |ρ| ≤ 1 →
        ∀ (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ),
        GaussianNoise μ ε (900*(1-ρ^2)) →
        β^2 = 900*ρ^2*((m:ℝ)*(2*r)-1)/(16*((m:ℝ)*(2*r))) →
        ∀ᵐ ξ ∂μ, biasA (phaseOriginal r m hr) (centeredOutcomes phaseSize β ε ξ) = 0) :=
  CancellationModel.assemble gaussian_noise_moments CancellationModel.n2_proof

example : AronowAudit.P027.Wave1.CancellationModel.Target := cancellation_model_counterexample

end
end AronowAudit.P027.Wave1
