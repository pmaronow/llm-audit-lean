import AronowAudit.P002.Wave1.PrintedTheorem2Blueprint
import AronowAudit.P002.Wave1.PrintedTheorem2.N1
import AronowAudit.P002.Wave1.PrintedTheorem2.N2
import AronowAudit.P002.Wave1.PrintedTheorem2.N3
import AronowAudit.P002.Wave1.PrintedTheorem2.N4
import AronowAudit.P002.Wave1.PrintedTheorem2.N5
import AronowAudit.P002.Wave1.PrintedTheorem2.N6
import AronowAudit.P002.Wave1.PrintedTheorem2.N7
import AronowAudit.P002.Wave1.PrintedTheorem2.N8
import AronowAudit.P002.Wave1.PrintedTheorem2.N9
import AronowAudit.P002.Wave1.PrintedTheorem2.N10
import AronowAudit.P002.Wave1.PrintedTheorem2.N11

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- The universal closure of printed Theorem 2 is false. -/
theorem printed_theorem2_refuted :
    ¬ (∀ (k : ℕ) (δ e A B r α : ℝ),
      0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
      (0 < r ∧ r ≤ 1/2) → (0 < α ∧ α < 1) →
      Tendsto (fun n => infCoverageXi n k δ e A B r α)
        atTop (nhds (ENNReal.ofReal (1-α)))) :=
  AronowAudit.P002.Wave1.PrintedTheorem2.assemble
    PrintedTheorem2.n1_proof PrintedTheorem2.n2_proof PrintedTheorem2.n3_proof
    PrintedTheorem2.n4_proof PrintedTheorem2.n5_proof PrintedTheorem2.n6_proof
    PrintedTheorem2.n7_proof PrintedTheorem2.n8_proof PrintedTheorem2.n9_proof
    PrintedTheorem2.n10_proof PrintedTheorem2.n11_proof

end
end AronowAudit.P002.Wave1
