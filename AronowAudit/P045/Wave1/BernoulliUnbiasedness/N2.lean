import AronowAudit.P045.Wave1.BernoulliUnbiasednessBlueprint

/-!
P045-T25: the own-treatment marginal means in the four-unit Bernoulli counterexample.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.BernoulliUnbiasedness

open AronowAudit.P045

/-- Every fair-Bernoulli own-treatment marginal of `coMembers` is `3/2`. -/
theorem n2_proof : N2 := by
  simp only [N2, co_members_marginal_four (1/2) (by norm_num) (by norm_num), mean]
  norm_num

end AronowAudit.P045.Wave1.BernoulliUnbiasedness
