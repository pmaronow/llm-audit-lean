import AronowAudit.P031.Wave1.FootnoteThreeProbabilityBlueprint
import AronowAudit.P031.Wave1.FootnoteThreeProbability.N1
import AronowAudit.P031.Wave1.FootnoteThreeProbability.N2
import AronowAudit.P031.Wave1.FootnoteThreeProbability.N3
import AronowAudit.P031.Wave1.FootnoteThreeProbability.N4
import AronowAudit.P031.Wave1.FootnoteThreeProbability.N5
import AronowAudit.P031.Wave1.FootnoteThreeProbability.N6
import AronowAudit.P031.Wave1.FootnoteThreeProbability.N7
import AronowAudit.P031.Wave1.FootnoteThreeProbability.N8
import AronowAudit.P031.Wave1.FootnoteThreeProbability.N9

namespace AronowAudit.P031.Wave1
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

/-- The stochastic clauses of corrected footnote 3, on the actual finite designs. -/
theorem footnote_three_probability_complete :
  ∀ (P : ℕ → Population), GrowingPopulations P →
    ∀ (p v1 v0 c : ℝ), 0 < p → p < 1 →
    Tendsto (fun n => ((P n).M : ℝ) / (P n).N) atTop (nhds p) →
    Tendsto (fun n => popVariance (P n).y1) atTop (nhds v1) →
    Tendsto (fun n => popVariance (P n).y0) atTop (nhds v0) →
    Tendsto (fun n => popCovariance (P n).y1 (P n).y0) atTop (nhds c) →
    (UniformlyBoundedOutcomes P → ArmSecondMomentsConverge P) ∧
    ((ArmSecondMomentsConverge P ∨ UniformlyBoundedOutcomes P) →
      ConvergesInProbability P (fun Q s => (Q.N : ℝ) * olsEstimator Q s)
        (v1 / (1 - p) + v0 / p) ∧
      (0 < (1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c →
        ConvergesInProbability P (fun Q s => olsEstimator Q s / trueVariance Q)
          ((v1 / (1 - p) + v0 / p) / ((1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c)))) := by
  exact FootnoteThreeProbability.assemble
    FootnoteThreeProbability.n1_proof FootnoteThreeProbability.n2_proof
    FootnoteThreeProbability.n3_proof FootnoteThreeProbability.n4_proof
    FootnoteThreeProbability.n5_proof FootnoteThreeProbability.n6_proof
    FootnoteThreeProbability.n7_proof FootnoteThreeProbability.n8_proof
    FootnoteThreeProbability.n9_proof

end
end AronowAudit.P031.Wave1
