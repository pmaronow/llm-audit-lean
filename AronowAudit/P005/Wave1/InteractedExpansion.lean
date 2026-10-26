import AronowAudit.P005.Wave1.InteractedExpansionBlueprint
import AronowAudit.P005.Wave1.InteractedExpansion.N1
import AronowAudit.P005.Wave1.InteractedExpansion.N2
import AronowAudit.P005.Wave1.InteractedExpansion.N3
import AronowAudit.P005.Wave1.InteractedExpansion.N4
import AronowAudit.P005.Wave1.InteractedExpansion.N5
import AronowAudit.P005.Wave1.InteractedExpansion.N6
import AronowAudit.P005.Wave1.InteractedExpansion.N7
import AronowAudit.P005.Wave1.InteractedExpansion.N8
import AronowAudit.P005.Wave1.InteractedExpansion.N9
import AronowAudit.P005.Wave1.InteractedExpansion.N10
import AronowAudit.P005.Wave1.InteractedExpansion.N11

set_option autoImplicit false
namespace AronowAudit.P005.Wave1
open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology
noncomputable section

/-- The literal printed logarithm condition allows a univariate spike population
whose interacted-regression remainder diverges along the even subsequence. -/
theorem printed_interacted_expansion_refuted :
    ¬ ∀ (d m : ℕ → ℕ) (P : (n : ℕ) → Population n (d n)), standingAssumptions d m P →
      (∀ᶠ n in atTop, interactedRegular (P n) (m n)) →
      Tendsto (fun n => kappa (P n) * Real.log (d n)) atTop (nhds 0) →
      stochasticO m (fun n S => interactedATE (P n) S - ate (P n) - armLeading (P n) S)
        (fun n => Real.sqrt (kappa (P n) * (d n) / n)) :=
  InteractedExpansion.assemble
    InteractedExpansion.n1_proof InteractedExpansion.n2_proof InteractedExpansion.n3_proof
    InteractedExpansion.n4_proof InteractedExpansion.n5_proof InteractedExpansion.n6_proof
    InteractedExpansion.n7_proof InteractedExpansion.n8_proof InteractedExpansion.n9_proof
    InteractedExpansion.n10_proof InteractedExpansion.n11_proof

end
end AronowAudit.P005.Wave1
