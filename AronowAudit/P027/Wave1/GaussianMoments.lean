import AronowAudit.P027.Wave1.GaussianMomentsBlueprint
import AronowAudit.P027.Wave1.GaussianMoments.N1
import AronowAudit.P027.Wave1.GaussianMoments.N2

namespace AronowAudit.P027.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable

theorem gaussian_noise_moments
    {Ξ K : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (ε : K → Ξ → ℝ) (σ2 : ℝ) :
    0 ≤ σ2 → GaussianNoise μ ε σ2 → NoiseMoments μ ε σ2 :=
  GaussianMoments.assemble GaussianMoments.n1_proof GaussianMoments.n2_proof μ ε σ2

end
end AronowAudit.P027.Wave1
