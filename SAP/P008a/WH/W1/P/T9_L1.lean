import SAP.P008a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008a.WH.W1.P.T9_L1

lemma coordinate_sq_diff_le_16 (x y : ℝ)
    (hx0 : 0 ≤ x) (hx4 : x ≤ 4) (hy0 : 0 ≤ y) (hy4 : y ≤ 4) :
    (x - y) ^ 2 ≤ 16 := by
  have hlo : -4 ≤ x - y := by linarith
  have hhi : x - y ≤ 4 := by linarith
  nlinarith [mul_nonneg (show 0 ≤ 4 + (x - y) by linarith)
    (show 0 ≤ 4 - (x - y) by linarith)]

end SAP.P008a.WH.W1.P.T9_L1

theorem SAP.P008a.WH.W1.T9_L1_proof : SAP.P008a.WH.W1.T9_L1 := by
  change SAP.P008a.WholeBoxBound
  intro p hp i l
  have h0 := SAP.P008a.WH.W1.P.T9_L1.coordinate_sq_diff_le_16
    (p i 0) (p l 0) (hp i 0).1 (hp i 0).2 (hp l 0).1 (hp l 0).2
  have h1 := SAP.P008a.WH.W1.P.T9_L1.coordinate_sq_diff_le_16
    (p i 1) (p l 1) (hp i 1).1 (hp i 1).2 (hp l 1).1 (hp l 1).2
  have hsum : ∑ a : Fin 2, (p i a - p l a) ^ 2 ≤ 32 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.succ_zero_eq_one]
    nlinarith
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Real.dist_eq, sq_abs]
  exact hsum
