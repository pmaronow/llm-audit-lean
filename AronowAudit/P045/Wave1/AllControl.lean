import AronowAudit.P045.Wave1.AllControlBlueprint
import AronowAudit.P045.Wave1.AllControl.N1

/-!
P045-T27: refutation of the documented all-untreated equivalence.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1

open AronowAudit.P045 Finset
open scoped BigOperators

/-- The coded indicator is not equivalent to the documented all-untreated condition. -/
theorem all_control_as_documented_refuted :
  ¬ ∀ {n : ℕ} (A : Network n) (z : Assignment n) (i : Fin n),
    badAllControl A.adj z i ↔ ∀ j ∈ neighborhood A.adj i, z j=false := by
  exact AllControl.assemble
    AllControl.n1_proof

end AronowAudit.P045.Wave1
