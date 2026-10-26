import AronowAudit.P045.Wave1.BernoulliUnbiasednessBlueprint

/-!
P045-T25: the conditional treated-arm mean in the four-unit Bernoulli counterexample.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.BernoulliUnbiasedness

open AronowAudit.P045

/-- The fair-Bernoulli conditional treated-arm mean of `coMembers` is `17/15`. -/
theorem n1_proof : N1 := by
  rw [N1, bernoulli_arm_count_conditional,
    show countDomain true = fun k : Fin 5 => 0 < k.val from funext fun k => by simp [countDomain]]
  exact bernoulli_count_counterexample.2.2.1

end AronowAudit.P045.Wave1.BernoulliUnbiasedness
