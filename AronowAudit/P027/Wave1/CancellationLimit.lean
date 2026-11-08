import AronowAudit.P027.Wave1.CancellationLimitBlueprint
import AronowAudit.P027.Wave1.GaussianMoments
import AronowAudit.P027.Wave1.CancellationLimit.N2
import AronowAudit.P027.Wave1.CancellationLimit.N3
import AronowAudit.P027.Wave1.CancellationLimit.N4
import AronowAudit.P027.Wave1.CancellationLimit.N5
import AronowAudit.P027.Wave1.CancellationLimit.N6
import AronowAudit.P027.Wave1.CancellationLimit.N7
import AronowAudit.P027.Wave1.CancellationLimit.N8
import AronowAudit.P027.Wave1.CancellationLimit.N9
import AronowAudit.P027.Wave1.CancellationLimit.N10

namespace AronowAudit.P027.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
attribute [local instance] Classical.propDecidable

/-- The corrected calibrated mean-scale limit, valid under the stated moments. -/
theorem periodic_calibrated_bias_in_measure : CancellationLimit.CalibratedInMeasure :=
  CancellationLimit.calibrated_in_measure CancellationLimit.n2_proof CancellationLimit.n3_proof
    CancellationLimit.n4_proof CancellationLimit.n5_proof CancellationLimit.n6_proof
    CancellationLimit.n7_proof

theorem cancellation_model_limit_counterexample :
    ¬ (∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (r : ℕ) (hr : 0 < r), r = 2 ∨ r = 10 → ∀ (ρ : ℝ), |ρ| ≤ 1 →
        ∀ (β : ℕ → ℝ) (ε : (n : ℕ) → (Σ _ : Fin r × Fin 2, Fin (n+1)) → Ξ → ℝ),
        (∀ n, GaussianNoise μ (ε n) (900*(1-ρ^2))) →
        (∀ n, (β n)^2 =
          900*ρ^2*((((n+1:ℕ):ℝ)*(2*r))-1)/(16*(((n+1:ℕ):ℝ)*(2*r)))) →
        TendstoInMeasure μ (fun n ξ => biasA (phaseOriginal r (n+1) hr)
            (centeredOutcomes phaseSize (β n) (ε n) ξ)) atTop (fun _ => 0) ∨
        TendstoInMeasure μ (fun n ξ => biasA (phaseOriginal r (n+1) hr)
            (centeredOutcomes phaseSize (β n) (ε n) ξ)/(((n+1:ℕ):ℝ)*(2*r))^2)
            atTop (fun _ => 0)) :=
  CancellationLimit.assemble gaussian_noise_moments CancellationLimit.n2_proof
    CancellationLimit.n3_proof CancellationLimit.n4_proof CancellationLimit.n5_proof
    CancellationLimit.n6_proof CancellationLimit.n7_proof CancellationLimit.n8_proof
    CancellationLimit.n9_proof CancellationLimit.n10_proof

example : AronowAudit.P027.Wave1.CancellationLimit.Target := cancellation_model_limit_counterexample

end
end AronowAudit.P027.Wave1
