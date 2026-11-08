import SAP.P025a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a.WH.W1.P.T2_L1
end SAP.P025a.WH.W1.P.T2_L1

open scoped BigOperators

theorem SAP.P025a.WH.W1.T2_L1_proof : SAP.P025a.WH.W1.T2_L1 := by
  change SAP.P025a.wholeClassTwoResiduals
  intro u v hu1 hu2 hv1 hv2
  have hden : 0 < u / 2 + v := by linarith
  have hden' : 0 < u + 2 * v := by linarith
  have hrel : u / 2 + v = (u + 2 * v) / 2 := by ring
  refine ⟨hden, ?_, ?_, ?_, ?_⟩
  · rw [hrel]
    field_simp [ne_of_gt hden']
    ring
  · rw [hrel]
    field_simp [ne_of_gt hden']
    ring
  · apply div_nonneg
    · nlinarith
    · positivity
  · apply div_nonneg
    · nlinarith
    · positivity
