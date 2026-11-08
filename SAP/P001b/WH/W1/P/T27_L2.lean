import SAP.P001b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P001b

theorem SAP.P001b.WH.W1.T27_L2_proof : SAP.P001b.WH.W1.T27_L2 := by
  change Set.range dyadicLocation = W1DyadicRationals
  ext x
  constructor
  · rintro ⟨⟨m, k⟩, rfl⟩
    simp only [W1DyadicRationals, Set.mem_setOf_eq, dyadicLocation]
    have hk : k.val < 2 ^ m := k.isLt
    have hnum : 2 * k.val + 1 < 2 ^ (m + 1) := by
      rw [pow_succ]
      omega
    have hnumR : (2 * k.val + 1 : ℕ) < 2 ^ (m + 1) := hnum
    constructor
    · positivity
    constructor
    · apply (div_lt_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (m + 1))).2
      exact_mod_cast hnumR
    · refine ⟨2 * k.val + 1, m + 1, ?_⟩
      push_cast
      rfl
  · intro hx
    simp only [W1DyadicRationals, Set.mem_setOf_eq] at hx
    rcases hx with ⟨hxpos, hxlt, a, n, hx⟩
    have hden : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have haR : (a : ℝ) < (2 : ℝ) ^ n := by
      rw [← div_lt_one hden]
      rw [hx] at hxlt
      exact hxlt
    have ha : a < 2 ^ n := by exact_mod_cast haR
    have ha0 : a ≠ 0 := by
      intro hzero
      rw [hx, hzero] at hxpos
      norm_num at hxpos
    obtain ⟨j, q, hqodd, hfactor⟩ := Nat.exists_eq_two_pow_mul_odd ha0
    obtain ⟨k, hqeq⟩ := hqodd
    have hqpos : 0 < q := by omega
    have hjlt : j < n := by
      by_contra hj
      have hnj : n ≤ j := Nat.le_of_not_gt hj
      have hpows : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by decide : 0 < 2) hnj
      have hpowle : 2 ^ j ≤ a := by
        calc
          2 ^ j = 2 ^ j * 1 := by simp
          _ ≤ 2 ^ j * q := Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (by omega))
          _ = a := hfactor.symm
      omega
    let m : ℕ := n - j - 1
    have hjle : j ≤ n := Nat.le_of_lt hjlt
    have hsub : j + (n - j) = n := Nat.add_sub_of_le hjle
    have hrem : n - j = m + 1 := by
      dsimp [m]
      omega
    have hexp : n = j + (m + 1) := by omega
    have hqbound : q < 2 ^ (m + 1) := by
      have hmulbound : 2 ^ j * q < 2 ^ j * 2 ^ (m + 1) := by
        have hha := ha
        rw [hexp, pow_add] at hha
        rw [hfactor] at hha
        exact hha
      exact Nat.lt_of_mul_lt_mul_left hmulbound
    have hqeq' : 2 * k + 1 = q := hqeq.symm
    have hoddBound : 2 * k + 1 < 2 ^ (m + 1) := by simpa [hqeq'] using hqbound
    have hk : k < 2 ^ m := by
      rw [pow_succ] at hoddBound
      omega
    have hxreduced : x = (q : ℝ) / (2 : ℝ) ^ (m + 1) := by
      calc
        x = (a : ℝ) / (2 : ℝ) ^ n := hx
        _ = ((2 : ℝ) ^ j * (q : ℝ)) /
              ((2 : ℝ) ^ j * (2 : ℝ) ^ (m + 1)) := by
          rw [hfactor, hexp, pow_add]
          push_cast
          rfl
        _ = (q : ℝ) / (2 : ℝ) ^ (m + 1) := by
          field_simp
    have hqreal : (q : ℝ) = 2 * (k : ℝ) + 1 := by
      rw [hqeq]
      push_cast
      ring
    rw [hqreal] at hxreduced
    refine ⟨⟨m, ⟨k, hk⟩⟩, ?_⟩
    change dyadicLocation ⟨m, ⟨k, hk⟩⟩ = x
    exact hxreduced.symm

