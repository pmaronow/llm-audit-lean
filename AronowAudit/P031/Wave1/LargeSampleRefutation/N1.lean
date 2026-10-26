import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint

/-! P031-T5: the witness sizes `N = 2^(4(n+1)²)` tend to infinity. -/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation

theorem n1_proof : N1 := by
  refine Filter.tendsto_atTop_mono (fun n => ?_) Filter.tendsto_id
  have h : n ≤ hcK n := by unfold hcK; nlinarith
  exact (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) h)

end AronowAudit.P031.Wave1.LargeSampleRefutation
