import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint
import AronowAudit.P031.Wave1.LargeSampleRefutation.N1
import AronowAudit.P031.Wave1.LargeSampleRefutation.N2
import AronowAudit.P031.Wave1.LargeSampleRefutation.N3
import AronowAudit.P031.Wave1.LargeSampleRefutation.N4
import AronowAudit.P031.Wave1.LargeSampleRefutation.N5
import AronowAudit.P031.Wave1.LargeSampleRefutation.N6
import AronowAudit.P031.Wave1.LargeSampleRefutation.N7
import AronowAudit.P031.Wave1.LargeSampleRefutation.N8
import AronowAudit.P031.Wave1.LargeSampleRefutation.N9
import AronowAudit.P031.Wave1.LargeSampleRefutation.N10
import AronowAudit.P031.Wave1.LargeSampleRefutation.N11
import AronowAudit.P031.Wave1.LargeSampleRefutation.N12
import AronowAudit.P031.Wave1.LargeSampleRefutation.N13
import AronowAudit.P031.Wave1.LargeSampleRefutation.N14
import AronowAudit.P031.Wave1.LargeSampleRefutation.N15
import AronowAudit.P031.Wave1.LargeSampleRefutation.N16
import AronowAudit.P031.Wave1.LargeSampleRefutation.N17
import AronowAudit.P031.Wave1.FootnoteThreeProbability.N7

/-! Counterexample to the universally quantified printed large-sample assertions. -/

namespace AronowAudit.P031.Wave1
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem printed_large_sample_contract_refuted :
    (∃ P : ℕ → Population,
      GrowingPopulations P ∧ StandardizedNormalLimit P ∧
      ¬ FirstOrderEquivalent P hrEstimator hc2Estimator) ∧
    ¬ (∀ P : ℕ → Population,
      GrowingPopulations P → StandardizedNormalLimit P →
      FirstOrderEquivalent P hrEstimator hc2Estimator ∧
      FirstOrderEquivalent P hc1Estimator hc2Estimator ∧
      FirstOrderEquivalent P hc3Estimator hc2Estimator ∧
      ∀ z : ℝ, 0 < z →
        ConservativeCoverage P neymanEstimator z ∧
        ConservativeCoverage P hc2Estimator z ∧
        ConservativeCoverage P hrEstimator z ∧
        ConservativeCoverage P hc1Estimator z ∧
        ConservativeCoverage P hc3Estimator z) := by
  exact AronowAudit.P031.Wave1.LargeSampleRefutation.assemble
    LargeSampleRefutation.n1_proof
    LargeSampleRefutation.n2_proof
    LargeSampleRefutation.n3_proof
    LargeSampleRefutation.n4_proof
    LargeSampleRefutation.n5_proof
    LargeSampleRefutation.n6_proof
    LargeSampleRefutation.n7_proof
    LargeSampleRefutation.n8_proof
    LargeSampleRefutation.n9_proof
    LargeSampleRefutation.n10_proof
    LargeSampleRefutation.n11_proof
    LargeSampleRefutation.n12_proof
    LargeSampleRefutation.n13_proof
    LargeSampleRefutation.n14_proof
    LargeSampleRefutation.n15_proof
    LargeSampleRefutation.n16_proof
    LargeSampleRefutation.n17_proof
    FootnoteThreeProbability.n7_proof

end
end AronowAudit.P031.Wave1
