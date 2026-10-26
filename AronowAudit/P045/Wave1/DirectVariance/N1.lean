import AronowAudit.P045.Wave1.DirectVarianceBlueprint

/-!
P045-T26: exact moments in the six-group additive counterexample.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.DirectVariance

open AronowAudit.P045

/-- At the six-group additive witness, `E vest = 1/3` and `Var point = 1/2`. -/
theorem n1_proof : N1 :=
  have h := singleton_variance_counterexample.1 2 (by simp)
  ⟨h.2.2, h.2.1⟩

end AronowAudit.P045.Wave1.DirectVariance
