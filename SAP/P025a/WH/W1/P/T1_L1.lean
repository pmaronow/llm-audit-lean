import SAP.P025a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a.WH.W1.P.T1_L1

private theorem firstNumerator_nonneg (u v : ℝ) (hu2 : u ≤ 2) (hv1 : 1 ≤ v) :
    0 ≤ (2 - u) + 2 * (v - 1) :=
  add_nonneg (by linarith) (mul_nonneg (by norm_num) (by linarith))

private theorem secondNumerator_nonneg (u v : ℝ) (hu1 : 1 ≤ u) (hv2 : v ≤ 2) :
    0 ≤ 2 * (u - 1) + (2 - v) :=
  add_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)

end SAP.P025a.WH.W1.P.T1_L1

theorem SAP.P025a.WH.W1.T1_L1_proof : SAP.P025a.WH.W1.T1_L1 := by
  intro u v hu1 hu2 hv1 hv2
  have huv : 0 < u + v := by linarith
  have hne : u + v ≠ 0 := ne_of_gt huv
  have hnum₁ := SAP.P025a.WH.W1.P.T1_L1.firstNumerator_nonneg u v hu2 hv1
  have hnum₂ := SAP.P025a.WH.W1.P.T1_L1.secondNumerator_nonneg u v hu1 hv2
  refine ⟨huv, ?_, ?_, ?_, ?_⟩
  · field_simp [hne]
    ring
  · field_simp [hne]
    ring
  · exact div_nonneg hnum₁ (by positivity)
  · exact div_nonneg hnum₂ (by positivity)
