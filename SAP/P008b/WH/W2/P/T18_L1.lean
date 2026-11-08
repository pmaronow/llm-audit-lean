import SAP.P008b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b.WH.W2.P.T18_L1

private lemma exp_mul_two (x : ℝ) : Real.exp (x * 2) = Real.exp x ^ 2 := by
  convert Real.exp_nat_mul x 2 using 1 <;> norm_num [mul_comm]

private lemma exp_mul_four (x : ℝ) : Real.exp (x * 4) = Real.exp x ^ 4 := by
  convert Real.exp_nat_mul x 4 using 1 <;> norm_num [mul_comm]

private lemma exp_mul_eight (x : ℝ) : Real.exp (x * 8) = Real.exp x ^ 8 := by
  convert Real.exp_nat_mul x 8 using 1 <;> norm_num [mul_comm]

private lemma exp_fifth_bounds :
    (1221402758 / 1000000000 : ℝ) < Real.exp (1 / 5) ∧
      Real.exp (1 / 5) < 1221402759 / 1000000000 := by
  have hb := Real.exp_bound (x := (1 / 5 : ℝ)) (by norm_num) (n := 12) (by norm_num)
  have hs : (∑ k ∈ Finset.range 12, ((1 / 5 : ℝ) ^ k / (Nat.factorial k : ℝ))) =
      (595147578331639 / 487265625000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [abs_le] at hb
  rw [hs] at hb
  norm_num [Nat.factorial] at hb
  constructor
  · linarith
  · linarith

private lemma exp_three_fifths_bounds :
    (1822118800 / 1000000000 : ℝ) < Real.exp (3 / 5) ∧
      Real.exp (3 / 5) < 1822118801 / 1000000000 := by
  have hb := Real.exp_bound (x := (3 / 5 : ℝ)) (by norm_num) (n := 12) (by norm_num)
  have hs : (∑ k ∈ Finset.range 12, ((3 / 5 : ℝ) ^ k / (Nat.factorial k : ℝ))) =
      (3131766688163 / 1718750000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [abs_le] at hb
  rw [hs] at hb
  norm_num [Nat.factorial] at hb
  constructor
  · linarith
  · linarith

private lemma kernel_between (r E L U : ℝ) (m : ℕ)
    (hr : 0 < r) (hL : 0 < L) (hU : 0 < U) (hm : 0 < m)
    (hEL : L < E) (hEU : E < U)
    (hrep : toyKernel r = 2 * (E⁻¹) ^ m - (128 / 3 : ℝ) * r ^ 4 * (E⁻¹) ^ (2 * m))
    {lo hi : ℝ}
    (hlo : lo < 2 * (U⁻¹) ^ m - (128 / 3 : ℝ) * r ^ 4 * (L⁻¹) ^ (2 * m))
    (hhi : 2 * (L⁻¹) ^ m - (128 / 3 : ℝ) * r ^ 4 * (U⁻¹) ^ (2 * m) < hi) :
    lo < toyKernel r ∧ toyKernel r < hi := by
  have hE : 0 < E := hL.trans hEL
  have hinvLo : U⁻¹ < E⁻¹ := (inv_lt_inv₀ hU hE).2 hEU
  have hinvHi : E⁻¹ < L⁻¹ := (inv_lt_inv₀ hE hL).2 hEL
  have hpLo : (U⁻¹) ^ m < (E⁻¹) ^ m :=
    pow_lt_pow_left₀ hinvLo (inv_nonneg.mpr hU.le) (Nat.ne_of_gt hm)
  have hpHi : (E⁻¹) ^ m < (L⁻¹) ^ m :=
    pow_lt_pow_left₀ hinvHi (inv_nonneg.mpr hE.le) (Nat.ne_of_gt hm)
  have h2m : 0 < 2 * m := Nat.mul_pos (by omega) hm
  have hp2Lo : (U⁻¹) ^ (2 * m) < (E⁻¹) ^ (2 * m) :=
    pow_lt_pow_left₀ hinvLo (inv_nonneg.mpr hU.le) (Nat.ne_of_gt h2m)
  have hp2Hi : (E⁻¹) ^ (2 * m) < (L⁻¹) ^ (2 * m) :=
    pow_lt_pow_left₀ hinvHi (inv_nonneg.mpr hE.le) (Nat.ne_of_gt h2m)
  have hB : 0 < (128 / 3 : ℝ) * r ^ 4 := by positivity
  have hmulLo : (128 / 3 : ℝ) * r ^ 4 * (E⁻¹) ^ (2 * m) <
      (128 / 3 : ℝ) * r ^ 4 * (L⁻¹) ^ (2 * m) :=
    mul_lt_mul_of_pos_left hp2Hi hB
  have hmulHi : (128 / 3 : ℝ) * r ^ 4 * (U⁻¹) ^ (2 * m) <
      (128 / 3 : ℝ) * r ^ 4 * (E⁻¹) ^ (2 * m) :=
    mul_lt_mul_of_pos_left hp2Lo hB
  have hlo' : 2 * (U⁻¹) ^ m - (128 / 3 : ℝ) * r ^ 4 * (L⁻¹) ^ (2 * m) <
      2 * (E⁻¹) ^ m - (128 / 3 : ℝ) * r ^ 4 * (E⁻¹) ^ (2 * m) := by
    nlinarith [hpLo, hmulLo]
  have hhi' : 2 * (E⁻¹) ^ m - (128 / 3 : ℝ) * r ^ 4 * (E⁻¹) ^ (2 * m) <
      2 * (L⁻¹) ^ m - (128 / 3 : ℝ) * r ^ 4 * (U⁻¹) ^ (2 * m) := by
    nlinarith [hpHi, hmulHi]
  constructor
  · rw [hrep]
    exact hlo.trans hlo'
  · rw [hrep]
    exact hhi'.trans hhi

private lemma rep_tenth :
    toyKernel (1 / 10) = 2 * ((Real.exp (1 / 5))⁻¹) ^ 1 -
      (128 / 3 : ℝ) * (1 / 10 : ℝ) ^ 4 * ((Real.exp (1 / 5))⁻¹) ^ 2 := by
  unfold toyKernel
  rw [show -2 * (1 / 10 : ℝ) = -(1 / 5 : ℝ) by norm_num,
    show -4 * (1 / 10 : ℝ) = -((1 / 5 : ℝ) * 2) by norm_num,
    Real.exp_neg, Real.exp_neg]
  rw [exp_mul_two (1 / 5 : ℝ)]
  simp only [inv_pow]
  norm_num

private lemma rep_one :
    toyKernel 1 = 2 * ((Real.exp 1)⁻¹) ^ 2 -
      (128 / 3 : ℝ) * (1 : ℝ) ^ 4 * ((Real.exp 1)⁻¹) ^ 4 := by
  unfold toyKernel
  rw [show -2 * (1 : ℝ) = -(1 * 2) by norm_num,
    show -4 * (1 : ℝ) = -(1 * 4) by norm_num,
    Real.exp_neg, Real.exp_neg,
    exp_mul_two (1 : ℝ), exp_mul_four (1 : ℝ)]
  simp only [inv_pow]

private lemma rep_six_fifths :
    toyKernel (6 / 5) = 2 * ((Real.exp (3 / 5))⁻¹) ^ 4 -
      (128 / 3 : ℝ) * (6 / 5 : ℝ) ^ 4 * ((Real.exp (3 / 5))⁻¹) ^ 8 := by
  unfold toyKernel
  rw [show -2 * (6 / 5 : ℝ) = -((3 / 5 : ℝ) * 4) by norm_num,
    show -4 * (6 / 5 : ℝ) = -((3 / 5 : ℝ) * 8) by norm_num,
    Real.exp_neg, Real.exp_neg,
    exp_mul_four (3 / 5 : ℝ), exp_mul_eight (3 / 5 : ℝ)]
  simp only [inv_pow]

private lemma rep_two :
    toyKernel 2 = 2 * ((Real.exp 1)⁻¹) ^ 4 -
      (128 / 3 : ℝ) * (2 : ℝ) ^ 4 * ((Real.exp 1)⁻¹) ^ 8 := by
  unfold toyKernel
  rw [show -2 * (2 : ℝ) = -(1 * 4) by norm_num,
    show -4 * (2 : ℝ) = -(1 * 8) by norm_num,
    Real.exp_neg, Real.exp_neg,
    exp_mul_four (1 : ℝ), exp_mul_eight (1 : ℝ)]
  simp only [inv_pow]

end SAP.P008b.WH.W2.P.T18_L1

theorem SAP.P008b.WH.W2.T18_L1_proof : SAP.P008b.WH.W2.T18_L1 := by
  rcases SAP.P008b.WH.W2.P.T18_L1.exp_fifth_bounds with ⟨h51, h52⟩
  rcases SAP.P008b.WH.W2.P.T18_L1.exp_three_fifths_bounds with ⟨h31, h32⟩
  have h1L : (27182818283 / 10000000000 : ℝ) < Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num at h ⊢
    exact h
  have h1U : Real.exp 1 < (27182818286 / 10000000000 : ℝ) := by
    have h := Real.exp_one_lt_d9
    norm_num at h ⊢
    exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := SAP.P008b.WH.W2.P.T18_L1.kernel_between (1 : ℝ) (Real.exp 1)
      (27182818283 / 10000000000) (27182818286 / 10000000000) 2
      (by norm_num) (by norm_num) (by norm_num) (by omega) h1L h1U
      (by simpa using SAP.P008b.WH.W2.P.T18_L1.rep_one)
      (lo := -100) (hi := -(21 / 50 : ℝ))
      (by norm_num) (by norm_num)
    exact h.2
  · have h := SAP.P008b.WH.W2.P.T18_L1.kernel_between (1 / 10 : ℝ)
      (Real.exp (1 / 5)) (1221402758 / 1000000000) (1221402759 / 1000000000) 1
      (by norm_num) (by norm_num) (by norm_num) (by omega) h51 h52
      (by simpa using SAP.P008b.WH.W2.P.T18_L1.rep_tenth)
      (lo := 325 / 200) (hi := 327 / 200)
      (by norm_num) (by norm_num)
    rcases h with ⟨hl, hu⟩
    rw [abs_lt]
    constructor <;> nlinarith
  · have h := SAP.P008b.WH.W2.P.T18_L1.kernel_between (6 / 5 : ℝ)
      (Real.exp (3 / 5)) (1822118800 / 1000000000) (1822118801 / 1000000000) 4
      (by norm_num) (by norm_num) (by norm_num) (by omega) h31 h32
      (by simpa using SAP.P008b.WH.W2.P.T18_L1.rep_six_fifths)
      (lo := -(111 / 200)) (hi := -(109 / 200))
      (by norm_num) (by norm_num)
    rcases h with ⟨hl, hu⟩
    rw [abs_lt]
    constructor <;> nlinarith
  · have h := SAP.P008b.WH.W2.P.T18_L1.kernel_between (2 : ℝ) (Real.exp 1)
      (27182818283 / 10000000000) (27182818286 / 10000000000) 4
      (by norm_num) (by norm_num) (by norm_num) (by omega) h1L h1U
      (by simpa using SAP.P008b.WH.W2.P.T18_L1.rep_two)
      (lo := -(39 / 200)) (hi := -(37 / 200))
      (by norm_num) (by norm_num)
    rcases h with ⟨hl, hu⟩
    rw [abs_lt]
    constructor <;> nlinarith
