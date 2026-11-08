import AronowAudit.P045.Wave1.BernoulliUnbiasednessBlueprint

/-! Node N2 of the P045-T25 refutation blueprint (trivial; proved by the blueprint author). -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.BernoulliUnbiasedness

open AronowAudit.P045

/-- Node N2: every fair-Bernoulli own-treatment marginal of `coMembers` is `3/2`. -/
theorem n2_proof : N2 := by
  simp only [N2, co_members_marginal_four (1/2) (by norm_num) (by norm_num), mean]
  norm_num

end AronowAudit.P045.Wave1.BernoulliUnbiasedness
