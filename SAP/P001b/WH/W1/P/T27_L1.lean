import SAP.P001b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b.WH.W1.P.T27_L1

private theorem no_lt_of_odd_pow_eq
    (a b p q : ℕ) (hb : Odd (2 * b + 1))
    (h : (2 * a + 1) * 2 ^ (q + 1) = (2 * b + 1) * 2 ^ (p + 1))
    (hpq : p < q) : False := by
  have hpq' : p + 1 ≤ q := by omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hpq'
  have hpow : 2 ^ (q + 1) = 2 ^ (p + 1) * 2 ^ (t + 1) := by
    rw [show q + 1 = (p + 1) + (t + 1) by omega, pow_add]
  rw [hpow] at h
  have hcancel : 2 ^ (p + 1) * ((2 * a + 1) * 2 ^ (t + 1)) =
      2 ^ (p + 1) * (2 * b + 1) := by
    calc
      2 ^ (p + 1) * ((2 * a + 1) * 2 ^ (t + 1)) =
          (2 * a + 1) * (2 ^ (p + 1) * 2 ^ (t + 1)) := by ac_rfl
      _ = (2 * b + 1) * 2 ^ (p + 1) := h
      _ = 2 ^ (p + 1) * (2 * b + 1) := by ac_rfl
  have hsmall : (2 * a + 1) * 2 ^ (t + 1) = 2 * b + 1 :=
    Nat.mul_left_cancel (by positivity) hcancel
  have hdiv : 2 ∣ 2 * b + 1 := by
    rw [← hsmall]
    refine ⟨(2 * a + 1) * 2 ^ t, ?_⟩
    rw [Nat.pow_succ]
    ring
  exact hb.not_two_dvd_nat hdiv

theorem odd_dyadic_eq
    (a b m n : ℕ)
    (h : (2 * a + 1) * 2 ^ (n + 1) = (2 * b + 1) * 2 ^ (m + 1)) :
    m = n ∧ a = b := by
  have ha : Odd (2 * a + 1) := ⟨a, by omega⟩
  have hb : Odd (2 * b + 1) := ⟨b, by omega⟩
  have hm : m = n := by
    by_contra hmn
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · exact (no_lt_of_odd_pow_eq a b m n hb h hlt).elim
    · exact (no_lt_of_odd_pow_eq b a n m ha h.symm hgt).elim
  subst n
  have hab : 2 * a + 1 = 2 * b + 1 :=
    Nat.mul_right_cancel (by positivity) h
  exact ⟨rfl, by omega⟩

end SAP.P001b.WH.W1.P.T27_L1

theorem SAP.P001b.WH.W1.T27_L1_proof : SAP.P001b.WH.W1.T27_L1 := by
  change Function.Injective SAP.P001b.dyadicLocation
  intro i j hij
  obtain ⟨m, a⟩ := i
  obtain ⟨n, b⟩ := j
  change (2 * (a : ℝ) + 1) / (2 : ℝ) ^ (m + 1) =
      (2 * (b : ℝ) + 1) / (2 : ℝ) ^ (n + 1) at hij
  have hcross : (2 * (a : ℝ) + 1) * (2 : ℝ) ^ (n + 1) =
      (2 * (b : ℝ) + 1) * (2 : ℝ) ^ (m + 1) := by
    exact (div_eq_div_iff
      (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
      (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))).mp hij
  have hnat : (2 * a.val + 1) * 2 ^ (n + 1) =
      (2 * b.val + 1) * 2 ^ (m + 1) := by
    exact_mod_cast hcross
  obtain ⟨hmn, hab⟩ :=
    SAP.P001b.WH.W1.P.T27_L1.odd_dyadic_eq a.val b.val m n hnat
  subst n
  have hab' : a = b := Fin.ext hab
  cases hab'
  rfl
