import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

noncomputable section
namespace SAP.P041.WH.W1.P.T7_L3

lemma gamma_coefficient_nat :
    Nat.factorial 98 * 2 ^ 98 * Nat.choose 196 98 =
      4 ^ 98 * Nat.doubleFactorial 195 := by
  have hchoose : Nat.choose 196 98 * Nat.factorial 98 * Nat.factorial 98 =
      Nat.factorial 196 := by
    exact Nat.choose_mul_factorial_mul_factorial (n := 196) (k := 98) (by omega)
  have hdf : Nat.doubleFactorial 196 = 2 ^ 98 * Nat.factorial 98 := by
    exact Nat.doubleFactorial_two_mul 98
  have hrel : Nat.choose 196 98 * Nat.factorial 98 =
      2 ^ 98 * Nat.doubleFactorial 195 := by
    apply Nat.mul_left_cancel (Nat.factorial_pos 98)
    calc
      Nat.factorial 98 * (Nat.choose 196 98 * Nat.factorial 98) =
          Nat.choose 196 98 * Nat.factorial 98 * Nat.factorial 98 := by ring
      _ = Nat.factorial 196 := hchoose
      _ = Nat.doubleFactorial 196 * Nat.doubleFactorial 195 :=
        Nat.factorial_eq_mul_doubleFactorial 195
      _ = (2 ^ 98 * Nat.factorial 98) * Nat.doubleFactorial 195 := by rw [hdf]
      _ = Nat.factorial 98 * (2 ^ 98 * Nat.doubleFactorial 195) := by ring
  calc
    Nat.factorial 98 * 2 ^ 98 * Nat.choose 196 98 =
        2 ^ 98 * (Nat.choose 196 98 * Nat.factorial 98) := by ring
    _ = 2 ^ 98 * (2 ^ 98 * Nat.doubleFactorial 195) := by rw [hrel]
    _ = 4 ^ 98 * Nat.doubleFactorial 195 := by norm_num [pow_mul]

end SAP.P041.WH.W1.P.T7_L3

theorem SAP.P041.WH.W1.T7_L3_proof : SAP.P041.WH.W1.T7_L3 := by
  intro t
  have hg99 : Real.Gamma 99 = (Nat.factorial 98 : ℝ) := by
    have harg : (99 : ℝ) = (98 : ℝ) + 1 := by norm_num
    rw [harg]
    exact Real.Gamma_nat_eq_factorial 98
  have hghalf : Real.Gamma (197 / 2) =
      (Nat.doubleFactorial 195 : ℝ) * Real.sqrt Real.pi / (2 : ℝ) ^ 98 := by
    convert Real.Gamma_nat_add_half 98 using 1 <;> norm_num
  have hsqpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hs197 : Real.sqrt (197 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hspi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hdf : (Nat.doubleFactorial 195 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.doubleFactorial_pos 195))
  have hchoose : (Nat.choose 196 98 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : 98 ≤ 196)))
  have hcoeff : (Nat.factorial 98 : ℝ) * 2 ^ 98 *
      (Nat.choose 196 98 : ℝ) = 4 ^ 98 * (Nat.doubleFactorial 195 : ℝ) := by
    have hc := congrArg (fun n : ℕ => (n : ℝ))
      SAP.P041.WH.W1.P.T7_L3.gamma_coefficient_nat
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
  have hroot : Real.sqrt (197 * Real.pi) = Real.sqrt 197 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 197)]
  have hconstant :
      Real.Gamma 99 / (Real.sqrt (197 * Real.pi) * Real.Gamma (197 / 2)) =
        (4 : ℝ) ^ 98 / ((Nat.choose 196 98 : ℝ) * Real.pi * Real.sqrt 197) := by
    rw [hg99, hghalf, hroot]
    field_simp [Real.pi_ne_zero, hs197, hspi, hdf, hchoose]
    nlinarith [hsqpi, hcoeff]
  have hpow : (1 + t ^ 2 / 197) ^ (-(99 : ℝ)) =
      ((1 + t ^ 2 / 197) ^ 99)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    norm_num [Real.rpow_natCast]
  unfold SAP.P041.Student197DensityW1 SAP.P041.Student197ConstantW1
  rw [hconstant, hpow]
  simp only [div_eq_mul_inv]
