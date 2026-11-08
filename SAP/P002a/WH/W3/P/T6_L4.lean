import SAP.P002a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W3.P.T6_L4

lemma eta_bounds (m : ℕ) (hm : 4 ≤ m) :
    0 < SAP.P002a.t6Eta m ∧ SAP.P002a.t6Eta m ≤ 1 / 4 := by
  have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ ((2 * m) ^ 2) := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  unfold SAP.P002a.t6Eta
  constructor
  · positivity
  · exact (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by nlinarith)

lemma t6T_bound (m : ℕ) (hm : 4 ≤ m) (i : Fin (2 * m)) :
    |SAP.P002a.t6T m i| ≤ 1 := by
  have hmpos : 0 < m := by omega
  have hmreal : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hd : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hmod := Nat.mod_lt i.val hmpos
  have hmodr : ((i.val % m : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hmod)
  rw [abs_le]
  constructor
  · dsimp [SAP.P002a.t6T]
    apply (le_div_iff₀ hd).mpr
    have hk0 : (0 : ℝ) ≤ (i.val % m : ℕ) := Nat.cast_nonneg _
    nlinarith
  · dsimp [SAP.P002a.t6T]
    apply (div_le_iff₀ hd).mpr
    nlinarith

lemma t6X_formula (m : ℕ) (i : Fin (2 * m)) :
    SAP.P002a.t6X m i =
      (if i.val < m then 1 else -1) + SAP.P002a.t6Eta m * SAP.P002a.t6T m i := rfl

lemma t6_mod_eq (m : ℕ) (hm : 4 ≤ m) (i j : Fin (2 * m))
    (h : SAP.P002a.t6T m i = SAP.P002a.t6T m j) : i.val % m = j.val % m := by
  have hmcast : (0 : ℝ) < (m : ℝ) - 1 := by
    have hmreal : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have he := congrArg (fun z : ℝ => z * ((m : ℝ) - 1)) h
  simp only [SAP.P002a.t6T, div_mul_cancel₀ _ hmcast.ne'] at he
  have hreal : ((i.val % m : ℕ) : ℝ) = ((j.val % m : ℕ) : ℝ) := by
    linarith
  exact_mod_cast hreal

end SAP.P002a.WH.W3.P.T6_L4

namespace SAP.P002a.WH.W3

theorem T6_L4_proof : T6_L4 := by
  intro m hm
  obtain ⟨heta0, heta1⟩ := SAP.P002a.WH.W3.P.T6_L4.eta_bounds m hm
  intro i j h
  have hiabs := abs_le.mp (SAP.P002a.WH.W3.P.T6_L4.t6T_bound m hm i)
  have hjabs := abs_le.mp (SAP.P002a.WH.W3.P.T6_L4.t6T_bound m hm j)
  have hip : -SAP.P002a.t6Eta m ≤ SAP.P002a.t6Eta m * SAP.P002a.t6T m i ∧
      SAP.P002a.t6Eta m * SAP.P002a.t6T m i ≤ SAP.P002a.t6Eta m := by
    constructor <;> nlinarith
  have hjp : -SAP.P002a.t6Eta m ≤ SAP.P002a.t6Eta m * SAP.P002a.t6T m j ∧
      SAP.P002a.t6Eta m * SAP.P002a.t6T m j ≤ SAP.P002a.t6Eta m := by
    constructor <;> nlinarith
  by_cases hi : i.val < m <;> by_cases hj : j.val < m
  · have he : SAP.P002a.t6Eta m * SAP.P002a.t6T m i =
        SAP.P002a.t6Eta m * SAP.P002a.t6T m j := by
      simpa only [SAP.P002a.WH.W3.P.T6_L4.t6X_formula, if_pos hi, if_pos hj, add_right_inj] using h
    have hmod := SAP.P002a.WH.W3.P.T6_L4.t6_mod_eq m hm i j (mul_left_cancel₀ heta0.ne' he)
    apply Fin.ext
    simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hmod
  · simp only [SAP.P002a.WH.W3.P.T6_L4.t6X_formula, if_pos hi, if_neg hj] at h
    linarith [hip.1, hjp.2]
  · simp only [SAP.P002a.WH.W3.P.T6_L4.t6X_formula, if_neg hi, if_pos hj] at h
    linarith [hjp.1, hip.2]
  · have he : SAP.P002a.t6Eta m * SAP.P002a.t6T m i =
        SAP.P002a.t6Eta m * SAP.P002a.t6T m j := by
      simpa only [SAP.P002a.WH.W3.P.T6_L4.t6X_formula, if_neg hi, if_neg hj, add_right_inj] using h
    have hmod := SAP.P002a.WH.W3.P.T6_L4.t6_mod_eq m hm i j (mul_left_cancel₀ heta0.ne' he)
    have him : i.val % m = i.val - m := by
      have hr : i.val = m + (i.val - m) := by omega
      calc
        i.val % m = (m + (i.val - m)) % m := congrArg (fun k => k % m) hr
        _ = i.val - m := by
          rw [Nat.add_mod]
          simp [Nat.mod_eq_of_lt (show i.val - m < m by have := i.isLt; omega)]
    have hjm : j.val % m = j.val - m := by
      have hr : j.val = m + (j.val - m) := by omega
      calc
        j.val % m = (m + (j.val - m)) % m := congrArg (fun k => k % m) hr
        _ = j.val - m := by
          rw [Nat.add_mod]
          simp [Nat.mod_eq_of_lt (show j.val - m < m by have := j.isLt; omega)]
    apply Fin.ext
    rw [him, hjm] at hmod
    omega

end SAP.P002a.WH.W3
