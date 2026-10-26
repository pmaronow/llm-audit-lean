import AronowAudit.P022.Wave1.FixedArmBlueprint

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.FixedArm
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem n1_proof : N1 := by
  intro N m k v1 v0 c M hm hk hN hv1 hv1M hv0 hv0M hc
  have hM : 0 ≤ M := hv1.trans hv1M
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hcM : |c| ≤ M := hc.trans <| (Real.sqrt_le_iff).2
    ⟨hM, by nlinarith [mul_le_mul hv1M hv0M hv0 hM]⟩
  have hmC : 0 ≤ 1 - 1 / (m : ℝ) ∧ 1 - 1 / (m : ℝ) ≤ 1 := by
    constructor
    · have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hmR
      norm_num at this
      exact sub_nonneg.mpr (by simpa only [one_div] using this)
    · exact sub_le_self _ (by positivity)
  have hkC : 0 ≤ 1 - 1 / (k : ℝ) ∧ 1 - 1 / (k : ℝ) ≤ 1 := by
    constructor
    · have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hkR
      norm_num at this
      exact sub_nonneg.mpr (by simpa only [one_div] using this)
    · exact sub_le_self _ (by positivity)
  have h1 : |(1 - 1 / (m : ℝ)) * v1| ≤ M := by
    rw [abs_of_nonneg (mul_nonneg hmC.1 hv1)]
    exact (mul_le_of_le_one_left hv1 hmC.2).trans hv1M
  have h0 : |(1 - 1 / (k : ℝ)) * v0| ≤ M := by
    rw [abs_of_nonneg (mul_nonneg hkC.1 hv0)]
    exact (mul_le_of_le_one_left hv0 hkC.2).trans hv0M
  rw [independent_means_remainder N m k v1 v0 c (by omega) (by omega) hN,
    abs_div, abs_of_pos (show 0 < (N : ℝ) - 1 by linarith)]
  apply div_le_div_of_nonneg_right _ (by linarith)
  rcases abs_le.mp hcM with ⟨hcl, hcu⟩
  rcases abs_le.mp h1 with ⟨h1l, h1u⟩
  rcases abs_le.mp h0 with ⟨h0l, h0u⟩
  apply abs_le.mpr
  constructor <;> linarith


end
end AronowAudit.P022.Wave1.FixedArm
