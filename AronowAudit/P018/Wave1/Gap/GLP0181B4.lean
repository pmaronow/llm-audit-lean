import AronowAudit.P018.Wave1.Gap.GP0182B2b

/-!
P018-T27: Proposition 1 with the printed assumptions.

Common-directed-kernel weighted consistency specializes to `singleRecord K`
with unit weights. It identifies the sample estimator and the unconditional
target with the original statistics, using positive definiteness of the
population Gram under `Standing`. The conclusion needs no additional
sample-rank or fitted-moment assumptions.
-/

noncomputable section
namespace AronowAudit.P018.Wave1

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem proposition1_printed_proof {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (hrank : SampleRank K) (hextra : Proposition1Extra K) :
    inProbability (unitSampleLaw K) (fun N ω =>
      (N : ℝ) • sampleVariance members (design K ω) (response K ω) - trueTarget K N) := by
  exact GP0182B2b_variance_consistency K hK

end AronowAudit.P018.Wave1
