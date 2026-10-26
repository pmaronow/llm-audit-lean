import AronowAudit.P018.Wave1.PrintedScalarCorollariesBlueprint
import AronowAudit.P018.Wave1.PrintedScalarCorollaries.N1
import AronowAudit.P018.Wave1.PrintedScalarCorollaries.N2

set_option autoImplicit false

namespace AronowAudit.P018.Wave1
open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
noncomputable section

theorem printed_corollaries_scalar_refuted :
  ¬ (Tendsto (fun N : ℕ => (N : ℝ) * ProbabilityTheory.variance
      (fun ω => sampleOLS (design signKernel ω) (response signKernel ω) 0)
      (unitSampleLaw signKernel N) - 4 / Dreal N) atTop (𝓝 0) ∧
    inProbability (unitSampleLaw signKernel) (fun N ω =>
      (N : ℝ) * (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 -
        4 / Dreal N)) :=
  PrintedScalarCorollaries.assemble PrintedScalarCorollaries.n1_proof PrintedScalarCorollaries.n2_proof

end
end AronowAudit.P018.Wave1
