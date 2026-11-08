import AronowAudit.P045.Wave1.AllControlBlueprint

/-! Node N1 of the P045-T27 refutation blueprint (trivial; proved by the blueprint author). -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.AllControl

open AronowAudit.P045

/-- Node N1: at `edge2`, `(true,false)`, unit `0`, the coded indicator holds but the
documented all-untreated condition fails. -/
theorem n1_proof : N1 :=
  ⟨(full_neighborhood_counterexample.2.1 0).1,
    fun h => (full_neighborhood_counterexample.2.1 0).2 ((full_control_correct _ _ _).2 h)⟩

end AronowAudit.P045.Wave1.AllControl
