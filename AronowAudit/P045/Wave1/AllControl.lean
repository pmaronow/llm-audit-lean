import AronowAudit.P045.Wave1.AllControlBlueprint
import AronowAudit.P045.Wave1.AllControl.N1

/-! Final assembly of the AllControl refutation. The statement below is the
literal body of the blueprint's Target, not an abbreviation for it. -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1

open AronowAudit.P045 Finset
open scoped BigOperators

/-- Refutation of the exact frozen contract, from the blueprint nodes. -/
theorem all_control_as_documented_refuted :
  ¬ ∀ {n : ℕ} (A : Network n) (z : Assignment n) (i : Fin n),
    badAllControl A.adj z i ↔ ∀ j ∈ neighborhood A.adj i, z j=false := by
  exact AllControl.assemble
    AllControl.n1_proof

example : AronowAudit.P045.Wave1.AllControl.Target := all_control_as_documented_refuted

end AronowAudit.P045.Wave1
