import SAP.P042.WH.W1.Leaves
import AronowAudit.P042.P042_Turnout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042.WH.W1.P.T1_L1

end SAP.P042.WH.W1.P.T1_L1

theorem SAP.P042.WH.W1.T1_L1_proof : SAP.P042.WH.W1.T1_L1 := by
  intro z hzlo hzhi q
  have hdiag : Real.sqrt (1 / 400 : ℝ) = 1 / 20 := by
    rw [show (1 / 400 : ℝ) = (1 / 20) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs]
    norm_num
  have hs : (6123 : ℝ) / 100000 < Real.sqrt (3 / 800 : ℝ) ∧
      Real.sqrt (3 / 800 : ℝ) < 6124 / 100000 := by
    apply AronowAudit.P042.sqrt_enclosure <;> norm_num
  have hdiaglo : (19 : ℝ) / 200 ≤ z * Real.sqrt (1 / 400 : ℝ) := by
    rw [hdiag]
    nlinarith
  have hdiaghi : z * Real.sqrt (1 / 400 : ℝ) < (20 : ℝ) / 200 := by
    rw [hdiag]
    nlinarith
  have htrueLoMul := mul_le_mul hzlo hs.1.le
    (by norm_num : (0 : ℝ) ≤ (6123 : ℝ) / 100000)
    (by linarith : (0 : ℝ) ≤ z)
  have htrueLo : (24 : ℝ) / 200 < z * Real.sqrt (3 / 800 : ℝ) := by
    nlinarith [htrueLoMul]
  have htrueHiMul := mul_le_mul hzhi hs.2.le
    (Real.sqrt_nonneg (3 / 800 : ℝ))
    (by norm_num : (0 : ℝ) ≤ (49 : ℝ) / 25)
  have htrueHi : z * Real.sqrt (3 / 800 : ℝ) < (25 : ℝ) / 200 := by
    nlinarith [htrueHiMul]
  have habs : |(q : ℝ) / 200| = (|q| : ℝ) / 200 := by
    rw [abs_div, ← Int.cast_abs]
    norm_num
  constructor
  · change AronowAudit.P042.coversZero ((q : ℝ) / 200)
      (z * Real.sqrt (1 / 400 : ℝ)) ↔ |q| ≤ 19
    rw [AronowAudit.P042.covers_zero_iff_abs, habs]
    constructor
    · intro h
      have hlt : (|q| : ℝ) < 20 := by linarith
      have hi : |q| < 20 := by exact_mod_cast hlt
      omega
    · intro h
      have hi : (|q| : ℝ) ≤ 19 := by exact_mod_cast h
      linarith
  · change AronowAudit.P042.coversZero ((q : ℝ) / 200)
      (z * Real.sqrt (3 / 800 : ℝ)) ↔ |q| ≤ 24
    rw [AronowAudit.P042.covers_zero_iff_abs, habs]
    constructor
    · intro h
      have hlt : (|q| : ℝ) < 25 := by linarith
      have hi : |q| < 25 := by exact_mod_cast hlt
      omega
    · intro h
      have hi : (|q| : ℝ) ≤ 24 := by exact_mod_cast h
      linarith
