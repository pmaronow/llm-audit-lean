import AronowAudit.P013.Wave1.CorrectedCoverageBlueprint
import AronowAudit.P013.Wave1.CorrectedCoverage.N1
import AronowAudit.P013.Wave1.CorrectedCoverage.N2
import AronowAudit.P013.Wave1.CorrectedCoverage.N3
import AronowAudit.P013.Wave1.CorrectedCoverage.N4
import AronowAudit.P013.Wave1.CorrectedCoverage.N5
import AronowAudit.P013.Wave1.CorrectedCoverage.N6
import AronowAudit.P013.Wave1.CorrectedCoverage.N7
import AronowAudit.P013.Wave1.CorrectedCoverage.N8
import AronowAudit.P013.Wave1.CorrectedCoverage.N9
import AronowAudit.P013.Wave1.CorrectedCoverage.N10

set_option autoImplicit false

namespace AronowAudit.P013.Wave1

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Corrected Proposition 6.2 under precisely the frozen corrected premises.
The auxiliary N10 premise instance is independent of the general coverage proof. -/
theorem corrected_wald_coverage_bridge :
    ∀ S : ExperimentSequence, NestedPopulationSetup S → ComparisonBounded S →
      Condition5Genuine S → Condition6 S → LowerTailCondition S →
      ∀ α : ℝ, 0 < α → α < 1 → 1 - α ≤ liminf (seqCoverage S α) atTop := by
  exact AronowAudit.P013.Wave1.CorrectedCoverage.assemble
    AronowAudit.P013.Wave1.CorrectedCoverage.n1_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n2_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n3_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n4_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n5_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n6_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n7_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n8_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n9_proof

example : AronowAudit.P013.Wave1.CorrectedCoverage.Target := corrected_wald_coverage_bridge

end

end AronowAudit.P013.Wave1
