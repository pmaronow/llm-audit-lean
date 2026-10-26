import AronowAudit.P013.Wave1.PrintedWaldBlueprint
import AronowAudit.P013.Wave1.CorrectedCoverage.N1
import AronowAudit.P013.Wave1.CorrectedCoverage.N2
import AronowAudit.P013.Wave1.CorrectedCoverage.N3
import AronowAudit.P013.Wave1.CorrectedCoverage.N4
import AronowAudit.P013.Wave1.CorrectedCoverage.N5
import AronowAudit.P013.Wave1.CorrectedCoverage.N6
import AronowAudit.P013.Wave1.CorrectedCoverage.N7
import AronowAudit.P013.Wave1.PrintedWald.N1
import AronowAudit.P013.Wave1.PrintedWald.N2
import AronowAudit.P013.Wave1.PrintedWald.N3
import AronowAudit.P013.Wave1.PrintedWald.N4
import AronowAudit.P013.Wave1.PrintedWald.N5
import AronowAudit.P013.Wave1.PrintedWald.N6
import AronowAudit.P013.Wave1.PrintedWald.N7
import AronowAudit.P013.Wave1.PrintedWald.N8
import AronowAudit.P013.Wave1.PrintedWald.N9
import AronowAudit.P013.Wave1.PrintedWald.N10
import AronowAudit.P013.Wave1.PrintedWald.N11
import AronowAudit.P013.Wave1.PrintedWald.N12
import AronowAudit.P013.Wave1.PrintedWald.N13
import AronowAudit.P013.Wave1.PrintedWald.N14

set_option autoImplicit false

namespace AronowAudit.P013.Wave1

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- The printed universal Wald coverage claim fails under its stated hypotheses. -/
theorem printed_wald_coverage_refuted :
    ¬ ∀ S : ExperimentSequence, NestedPopulationSetup S → StandingPositivity S →
      Condition3 S → Condition5Printed S → Condition6 S →
        ∀ α : ℝ, 0 < α → α < 1 → 1 - α ≤ liminf (seqCoverage S α) atTop := by
  exact AronowAudit.P013.Wave1.PrintedWald.assemble
    CorrectedCoverage.n1_proof CorrectedCoverage.n2_proof CorrectedCoverage.n3_proof
    CorrectedCoverage.n4_proof CorrectedCoverage.n5_proof CorrectedCoverage.n6_proof
    CorrectedCoverage.n7_proof
    PrintedWald.n1_proof PrintedWald.n2_proof PrintedWald.n3_proof PrintedWald.n4_proof
    PrintedWald.n5_proof PrintedWald.n6_proof PrintedWald.n7_proof PrintedWald.n8_proof
    PrintedWald.n9_proof PrintedWald.n10_proof PrintedWald.n11_proof PrintedWald.n12_proof
    PrintedWald.n13_proof PrintedWald.n14_proof

end

end AronowAudit.P013.Wave1
