import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P041.WH.W1.P.T7_L5

open SAP.P041.WH.W1

set_option maxRecDepth 10000 in
lemma choose_value :
    Nat.choose 196 98 = 5716592448890534420436582360196242777068052430850904489000 := by
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num : 98 ≤ 196)]
  norm_num

lemma rational_lower :
    (0.39843633174605 : ℝ)^2 * (Nat.choose 196 98 : ℝ)^2 *
        (3.14159265358979323847 : ℝ)^2 * 197 ≤ (4 : ℝ)^196 := by
  rw [choose_value]
  norm_num

lemma rational_upper :
    (4 : ℝ)^196 ≤ (0.39843633174607 : ℝ)^2 *
        (Nat.choose 196 98 : ℝ)^2 * (3.14159265358979323846 : ℝ)^2 * 197 := by
  rw [choose_value]
  norm_num

lemma constant_sq :
    Student197ConstantW1^2 =
      (4 : ℝ)^196 /
        ((Nat.choose 196 98 : ℝ)^2 * Real.pi^2 * 197) := by
  unfold Student197ConstantW1
  rw [div_pow, mul_pow, mul_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 197 by norm_num)]
  congr 1
  rw [← pow_mul]

lemma pi_sq_le_upper : Real.pi^2 ≤ (3.14159265358979323847 : ℝ)^2 := by
  exact (sq_le_sq₀ (le_of_lt Real.pi_pos) (by norm_num)).2 (le_of_lt Real.pi_lt_d20)

lemma lower_squared :
    (0.39843633174605 : ℝ)^2 ≤
      (4 : ℝ)^196 / ((Nat.choose 196 98 : ℝ)^2 * Real.pi^2 * 197) := by
  have hq : 0 < (Nat.choose 196 98 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by norm_num : 98 ≤ 196)
  apply (le_div_iff₀ (by positivity :
    0 < (Nat.choose 196 98 : ℝ)^2 * Real.pi^2 * 197)).2
  have hcoeff : 0 ≤ (0.39843633174605 : ℝ)^2 * (Nat.choose 196 98 : ℝ)^2 * 197 := by
    positivity
  have hbound :
      (0.39843633174605 : ℝ)^2 * (Nat.choose 196 98 : ℝ)^2 * Real.pi^2 * 197 ≤
        (0.39843633174605 : ℝ)^2 * (Nat.choose 196 98 : ℝ)^2 *
          (3.14159265358979323847 : ℝ)^2 * 197 := by
    nlinarith [mul_nonneg hcoeff
      (sub_nonneg.mpr pi_sq_le_upper)]
  nlinarith [rational_lower, hbound]

lemma pi_sq_ge_lower : (3.14159265358979323846 : ℝ)^2 ≤ Real.pi^2 := by
  exact (sq_le_sq₀ (by norm_num) (le_of_lt Real.pi_pos)).2 (le_of_lt Real.pi_gt_d20)

lemma upper_squared :
    (4 : ℝ)^196 / ((Nat.choose 196 98 : ℝ)^2 * Real.pi^2 * 197) ≤
      (0.39843633174607 : ℝ)^2 := by
  have hq : 0 < (Nat.choose 196 98 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by norm_num : 98 ≤ 196)
  apply (div_le_iff₀ (by positivity :
    0 < (Nat.choose 196 98 : ℝ)^2 * Real.pi^2 * 197)).2
  have hcoeff : 0 ≤ (0.39843633174607 : ℝ)^2 * (Nat.choose 196 98 : ℝ)^2 * 197 := by
    positivity
  have hbound :
      (0.39843633174607 : ℝ)^2 * (Nat.choose 196 98 : ℝ)^2 *
          (3.14159265358979323846 : ℝ)^2 * 197 ≤
        (0.39843633174607 : ℝ)^2 * (Nat.choose 196 98 : ℝ)^2 * Real.pi^2 * 197 := by
    nlinarith [mul_nonneg hcoeff
      (sub_nonneg.mpr pi_sq_ge_lower)]
  nlinarith [rational_upper, hbound]

end SAP.P041.WH.W1.P.T7_L5

theorem SAP.P041.WH.W1.T7_L5_proof : SAP.P041.WH.W1.T7_L5 := by
  unfold SAP.P041.WH.W1.T7_L5
  have hC : 0 ≤ SAP.P041.Student197ConstantW1 := by
    unfold SAP.P041.Student197ConstantW1
    positivity
  constructor
  · apply (sq_le_sq₀ (by norm_num) hC).mp
    rw [SAP.P041.WH.W1.P.T7_L5.constant_sq]
    exact SAP.P041.WH.W1.P.T7_L5.lower_squared
  · apply (sq_le_sq₀ hC (by norm_num)).mp
    rw [SAP.P041.WH.W1.P.T7_L5.constant_sq]
    exact SAP.P041.WH.W1.P.T7_L5.upper_squared
