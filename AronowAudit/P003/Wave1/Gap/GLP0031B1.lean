import AronowAudit.P003.P003_Audit

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-- Binomial coefficients with zero extension to negative integer indices. -/
noncomputable def discordant_estimator_sd_binom (n : ℕ) (k : ℤ) : ℝ :=
  if 0 ≤ k then (n.choose k.toNat : ℝ) else 0

local notation "B" => discordant_estimator_sd_binom

lemma discordant_estimator_sd_binom_nat (n k : ℕ) : B n k = n.choose k := by
  simp [discordant_estimator_sd_binom]

lemma discordant_estimator_sd_binom_nonneg (n : ℕ) (k : ℤ) : 0 ≤ B n k := by
  unfold discordant_estimator_sd_binom
  split_ifs <;> positivity

lemma discordant_estimator_sd_binom_zero (n : ℕ) (k : ℤ)
    (h : k < 0 ∨ (n : ℤ) < k) : B n k = 0 := by
  rcases h with h | h
  · simp [discordant_estimator_sd_binom, not_le.mpr h]
  · by_cases hk : 0 ≤ k
    · have hnk : n < k.toNat := by omega
      simp [discordant_estimator_sd_binom, hk, Nat.choose_eq_zero_of_lt hnk]
    · simp [discordant_estimator_sd_binom, hk]

lemma discordant_estimator_sd_binom_symm (n : ℕ) (k : ℤ) :
    B n ((n : ℤ)-k) = B n k := by
  by_cases hk : 0 ≤ k ∧ k ≤ n
  · obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hk.1
    rw [← Nat.cast_sub (by exact_mod_cast hk.2)]
    simp only [discordant_estimator_sd_binom_nat]
    exact_mod_cast Nat.choose_symm (by exact_mod_cast hk.2 : r ≤ n)
  · rw [discordant_estimator_sd_binom_zero n k (by omega),
      discordant_estimator_sd_binom_zero n ((n : ℤ)-k) (by omega)]

lemma discordant_estimator_sd_binom_summable (n : ℕ) (f : ℤ → ℝ) :
    Summable (fun k => B n k * f k) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc (0 : ℤ) n)
  intro k hk
  have hz := discordant_estimator_sd_binom_zero n k (by
    simp only [Finset.mem_Icc] at hk
    omega)
  simp [hz]

lemma discordant_estimator_sd_binom_pascal (n : ℕ) (k : ℤ) :
    B (n+1) k = B n k + B n (k-1) := by
  by_cases hk : k < 0
  · rw [discordant_estimator_sd_binom_zero _ _ (Or.inl hk),
      discordant_estimator_sd_binom_zero _ _ (Or.inl hk),
      discordant_estimator_sd_binom_zero _ _ (Or.inl (by omega))]
    ring
  have hk' : 0 ≤ k := by omega
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hk'
  cases r with
  | zero => simp [discordant_estimator_sd_binom]
  | succ r =>
    rw [show ((r+1 : ℕ) : ℤ)-1 = (r : ℤ) by push_cast; ring]
    simp only [discordant_estimator_sd_binom_nat]
    exact_mod_cast (Nat.choose_succ_succ n r).trans (Nat.add_comm _ _)

lemma discordant_estimator_sd_binom_select (n : ℕ) (k : ℤ) :
    (k : ℝ) * B (n+1) k = (n+1 : ℕ) * B n (k-1) := by
  by_cases hk : k < 0
  · rw [discordant_estimator_sd_binom_zero _ _ (Or.inl hk),
      discordant_estimator_sd_binom_zero _ _ (Or.inl (by omega))]
    ring
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ k)
  cases r with
  | zero => simp [discordant_estimator_sd_binom]
  | succ r =>
    rw [show ((r+1 : ℕ) : ℤ)-1 = (r : ℤ) by push_cast; ring]
    simp only [discordant_estimator_sd_binom_nat, Int.cast_natCast]
    have h := Nat.add_one_mul_choose_eq n r
    exact_mod_cast (Nat.mul_comm (r+1) ((n+1).choose (r+1))).trans h.symm

lemma discordant_estimator_sd_binom_omit (n : ℕ) (k : ℤ) :
    ((n+1 : ℕ) - (k : ℝ)) * B (n+1) k = (n+1 : ℕ) * B n k := by
  have h := discordant_estimator_sd_binom_select n ((n+1 : ℕ)-k)
  rw [discordant_estimator_sd_binom_symm] at h
  rw [show ((n+1 : ℕ) : ℤ)-k-1 = (n : ℤ)-k by push_cast; ring,
    discordant_estimator_sd_binom_symm] at h
  push_cast at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

lemma discordant_estimator_sd_binom_right (n : ℕ) (k : ℤ) (hk : (n : ℤ) ≤ 2*k) :
    B n (k+1) ≤ B n k := by
  by_cases hkn : (n : ℤ) < k+1
  · rw [discordant_estimator_sd_binom_zero _ _ (Or.inr hkn)]
    exact discordant_estimator_sd_binom_nonneg _ _
  have hk0 : 0 ≤ k := by omega
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  have hr : r+1 ≤ n := by omega
  have heq := Nat.choose_succ_right_eq n r
  have hnr : n-r ≤ r+1 := by omega
  have hle : n.choose (r+1) ≤ n.choose r := by nlinarith [Nat.choose_pos hr]
  rw [show (r : ℤ)+1 = ((r+1 : ℕ) : ℤ) by push_cast; ring]
  simpa only [discordant_estimator_sd_binom_nat] using (show (n.choose (r+1) : ℝ) ≤ n.choose r by exact_mod_cast hle)

lemma discordant_estimator_sd_binom_left (n : ℕ) (k : ℤ) (hk : 2*k ≤ (n : ℤ)) :
    B n (k-1) ≤ B n k := by
  have h := discordant_estimator_sd_binom_right n ((n : ℤ)-k) (by omega)
  rw [show (n : ℤ)-k+1 = (n : ℤ)-(k-1) by ring,
    discordant_estimator_sd_binom_symm, discordant_estimator_sd_binom_symm] at h
  exact h

lemma discordant_estimator_sd_binom_right_weak (n : ℕ) (k : ℤ)
    (hk : (n : ℤ)+1 ≤ 2*k) : B n k ≤ B n (k-1) := by
  by_cases h : (n : ℤ) ≤ 2*(k-1)
  · simpa using discordant_estimator_sd_binom_right n (k-1) h
  · have hn : (n : ℤ) = 2*k-1 := by omega
    have hsym := discordant_estimator_sd_binom_symm n k
    rw [show (n : ℤ)-k = k-1 by omega] at hsym
    exact le_of_eq hsym.symm

lemma discordant_estimator_sd_binom_left_weak (n : ℕ) (k : ℤ)
    (hk : 2*k ≤ (n : ℤ)-1) : B n k ≤ B n (k+1) := by
  have h := discordant_estimator_sd_binom_right_weak n ((n : ℤ)-k) (by omega)
  rw [show (n : ℤ)-k-1 = (n : ℤ)-(k+1) by ring,
    discordant_estimator_sd_binom_symm, discordant_estimator_sd_binom_symm] at h
  exact h

/-- Number of assignments with `t` treated labels and canonical scaled sum `s`. -/
noncomputable def discordant_estimator_sd_count (a d z : ℕ) (t s : ℤ) : ℝ :=
  ∑' x : ℤ, B a x * (B d (s+a-2*x) * B z (t+x-s-a))

local notation "C" => discordant_estimator_sd_count


lemma discordant_estimator_sd_count_symm (a d z m : ℕ) (hn : a+d+z = 2*m) (s : ℤ) :
    C a d z m ((d : ℤ)-s) = C a d z m s := by
  let e : ℤ ≃ ℤ := Equiv.subLeft a
  rw [discordant_estimator_sd_count, ← e.tsum_eq]
  apply tsum_congr
  intro x
  dsimp [e]
  change B a ((a : ℤ)-x) *
    (B d ((d : ℤ)-s+a-2*((a : ℤ)-x)) * B z ((m : ℤ)+((a : ℤ)-x)-((d : ℤ)-s)-a)) = _
  rw [discordant_estimator_sd_binom_symm]
  have hn' : (a : ℤ)+d+z = 2*m := by exact_mod_cast hn
  rw [show (d : ℤ)-s+a-2*((a : ℤ)-x) = (d : ℤ)-(s+a-2*x) by ring,
    discordant_estimator_sd_binom_symm]
  rw [show (m : ℤ)+((a : ℤ)-x)-((d : ℤ)-s)-a = (z : ℤ)-((m : ℤ)+x-s-a) by omega,
    discordant_estimator_sd_binom_symm]

lemma discordant_estimator_sd_binom_one (k : ℤ) :
    B 1 k = if k = 0 ∨ k = 1 then 1 else 0 := by
  by_cases h0 : k = 0
  · subst k; norm_num [discordant_estimator_sd_binom]
  by_cases h1 : k = 1
  · subst k; norm_num [discordant_estimator_sd_binom]
  rw [if_neg (by tauto), discordant_estimator_sd_binom_zero _ _ (by omega)]

lemma discordant_estimator_sd_binom_two (k : ℤ) :
    B 2 k = if k = 0 ∨ k = 2 then 1 else if k = 1 then 2 else 0 := by
  by_cases h0 : k = 0
  · subst k; norm_num [discordant_estimator_sd_binom]
  by_cases h1 : k = 1
  · subst k; norm_num [discordant_estimator_sd_binom]
  by_cases h2 : k = 2
  · subst k; norm_num [discordant_estimator_sd_binom]
  rw [if_neg (by tauto), if_neg h1, discordant_estimator_sd_binom_zero _ _ (by omega)]

lemma discordant_estimator_sd_one_even (a z : ℕ) (t s x : ℤ) (hx : s+a = 2*x) :
    C a 1 z t s = B a x * B z (t-x) := by
  unfold discordant_estimator_sd_count
  rw [tsum_eq_single x]
  · rw [show s+a-2*x = 0 by omega, discordant_estimator_sd_binom_one,
      show t+x-s-a = t-x by omega]
    norm_num
  · intro y hy
    rw [discordant_estimator_sd_binom_one, if_neg (by omega)]
    ring

lemma discordant_estimator_sd_one_odd (a z : ℕ) (t s x : ℤ) (hx : s+a = 2*x+1) :
    C a 1 z t s = B a x * B z (t-x-1) := by
  unfold discordant_estimator_sd_count
  rw [tsum_eq_single x]
  · rw [show s+a-2*x = 1 by omega, discordant_estimator_sd_binom_one,
      show t+x-s-a = t-x-1 by omega]
    norm_num
  · intro y hy
    rw [discordant_estimator_sd_binom_one, if_neg (by omega)]
    ring

lemma discordant_estimator_sd_two_even (a z : ℕ) (t s x : ℤ) (hx : s+a = 2*x) :
    C a 2 z t s = B a x * B z (t-x) + B a (x-1) * B z (t-x-1) := by
  unfold discordant_estimator_sd_count
  rw [tsum_eq_sum (s := {x, x-1}) (by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [discordant_estimator_sd_binom_two, if_neg (by omega), if_neg (by omega)]
    ring)]
  rw [Finset.sum_pair (by omega : x ≠ x-1)]
  rw [show s+a-2*x = 0 by omega, show s+a-2*(x-1) = 2 by omega,
    discordant_estimator_sd_binom_two, discordant_estimator_sd_binom_two,
    show t+x-s-a = t-x by omega, show t+(x-1)-s-a = t-x-1 by omega]
  norm_num

lemma discordant_estimator_sd_two_odd (a z : ℕ) (t s x : ℤ) (hx : s+a = 2*x+1) :
    C a 2 z t s = 2 * B a x * B z (t-x-1) := by
  unfold discordant_estimator_sd_count
  rw [tsum_eq_single x]
  · rw [show s+a-2*x = 1 by omega, discordant_estimator_sd_binom_two,
      show t+x-s-a = t-x-1 by omega]
    norm_num
    ring
  · intro y hy
    rw [discordant_estimator_sd_binom_two, if_neg (by omega), if_neg (by omega)]
    ring

lemma discordant_estimator_sd_one_step (a z m : ℕ) (hn : a+1+z = 2*m)
    (s : ℤ) (hs : 1 ≤ s) : C a 1 z m (s+1) ≤ C a 1 z m s := by
  have hn' : (a : ℤ)+1+z = 2*m := by exact_mod_cast hn
  let x := (s+a)/2
  have hx : s+a = 2*x ∨ s+a = 2*x+1 := by dsimp [x]; omega
  rcases hx with hx | hx
  · rw [discordant_estimator_sd_one_even a z m s x hx,
      discordant_estimator_sd_one_odd a z m (s+1) x (by omega)]
    exact mul_le_mul_of_nonneg_left
      (discordant_estimator_sd_binom_left z ((m : ℤ)-x) (by omega))
      (discordant_estimator_sd_binom_nonneg _ _)
  · rw [discordant_estimator_sd_one_odd a z m s x hx,
      discordant_estimator_sd_one_even a z m (s+1) (x+1) (by omega),
      show (m : ℤ)-(x+1) = (m : ℤ)-x-1 by ring]
    exact mul_le_mul_of_nonneg_right
      (discordant_estimator_sd_binom_right a x (by omega))
      (discordant_estimator_sd_binom_nonneg _ _)

lemma discordant_estimator_sd_two_step (a z m : ℕ) (hn : a+2+z = 2*m)
    (s : ℤ) (hs : 1 ≤ s) : C a 2 z m (s+1) ≤ C a 2 z m s := by
  have hn' : (a : ℤ)+2+z = 2*m := by exact_mod_cast hn
  let x := (s+a)/2
  have hx : s+a = 2*x ∨ s+a = 2*x+1 := by dsimp [x]; omega
  rcases hx with hx | hx
  · rw [discordant_estimator_sd_two_even a z m s x hx,
      discordant_estimator_sd_two_odd a z m (s+1) x (by omega)]
    have h1 := mul_le_mul_of_nonneg_left
      (discordant_estimator_sd_binom_left_weak z ((m : ℤ)-x-1) (by omega))
      (discordant_estimator_sd_binom_nonneg a x)
    have h2 := mul_le_mul_of_nonneg_right
      (discordant_estimator_sd_binom_right_weak a x (by omega))
      (discordant_estimator_sd_binom_nonneg z ((m : ℤ)-x-1))
    rw [show (m : ℤ)-x-1+1 = (m : ℤ)-x by ring] at h1
    linarith
  · rw [discordant_estimator_sd_two_odd a z m s x hx,
      discordant_estimator_sd_two_even a z m (s+1) (x+1) (by omega),
      show x+1-1 = x by ring, show (m : ℤ)-(x+1) = (m : ℤ)-x-1 by ring]
    have h1 := mul_le_mul_of_nonneg_right
      (discordant_estimator_sd_binom_right a x (by omega))
      (discordant_estimator_sd_binom_nonneg z ((m : ℤ)-x-1))
    have h2 := mul_le_mul_of_nonneg_left
      (discordant_estimator_sd_binom_left z ((m : ℤ)-x-1) (by omega))
      (discordant_estimator_sd_binom_nonneg a x)
    linarith

lemma discordant_estimator_sd_shape_of_step (f : ℤ → ℝ) (c : ℤ)
    (hsym : ∀ s, f (c-s) = f s)
    (hstep : ∀ s, c ≤ 2*s → f (s+1) ≤ f s) : SDShape f c := by
  refine ⟨hsym, ?_⟩
  intro i j hi hij
  exact Int.leInduction (motive := fun j _ => f j ≤ f i) le_rfl
    (fun j hji hj => (hstep j (by omega)).trans hj) j hij

lemma discordant_estimator_sd_one_shape (a z m : ℕ) (hn : a+1+z = 2*m) :
    SDShape (C a 1 z m) 1 := by
  apply discordant_estimator_sd_shape_of_step
  · exact discordant_estimator_sd_count_symm a 1 z m hn
  · intro s hs
    exact discordant_estimator_sd_one_step a z m hn s (by omega)

lemma discordant_estimator_sd_two_shape (a z m : ℕ) (hn : a+2+z = 2*m) :
    SDShape (C a 2 z m) 2 := by
  apply discordant_estimator_sd_shape_of_step
  · exact discordant_estimator_sd_count_symm a 2 z m hn
  · intro s hs
    exact discordant_estimator_sd_two_step a z m hn s (by omega)

lemma discordant_estimator_sd_binom_zero_top (k : ℤ) :
    B 0 k = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k; norm_num [discordant_estimator_sd_binom]
  · rw [if_neg hk, discordant_estimator_sd_binom_zero _ _ (by omega)]

lemma discordant_estimator_sd_binom_select_pred (n : ℕ) (k : ℤ) :
    (k : ℝ) * B n k = (n : ℝ) * B (n-1) (k-1) := by
  cases n with
  | zero => by_cases hk : k = 0 <;> simp [discordant_estimator_sd_binom_zero_top, hk]
  | succ n => simpa using discordant_estimator_sd_binom_select n k

lemma discordant_estimator_sd_binom_omit_pred (n : ℕ) (k : ℤ) :
    ((n : ℝ) - (k : ℝ)) * B n k = (n : ℝ) * B (n-1) k := by
  cases n with
  | zero => by_cases hk : k = 0 <;> simp [discordant_estimator_sd_binom_zero_top, hk]
  | succ n => simpa using discordant_estimator_sd_binom_omit n k

lemma discordant_estimator_sd_binom_shift_summable (n : ℕ) (r : ℤ) (f : ℤ → ℝ) :
    Summable (fun k => B n (k-r) * f k) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc r ((n : ℤ)+r))
  intro k hk
  rw [discordant_estimator_sd_binom_zero n (k-r) (by
    simp only [Finset.mem_Icc] at hk
    omega), zero_mul]

lemma discordant_estimator_sd_partner_term (a e z m : ℕ)
    (hn : a+(e+2)+z = 2*m) (x s : ℤ) :
    (m : ℝ) * (B a x * (B (e+2) (s+a-2*x) * B z ((m : ℤ)+x-s-a))) =
      (a : ℝ) *
        (B (a-1) x * (B (e+1) (s+a-2*x-1) * B z ((m : ℤ)+x-s-a)) +
          B (a-1) (x-1) * (B (e+1) (s+a-2*x) * B z ((m : ℤ)+x-s-a))) +
      (2*(e+1) : ℝ) * (B a x * (B e (s+a-2*x-1) * B z ((m : ℤ)+x-s-a))) +
      (z : ℝ) * (B a x *
        (B (e+1) (s+a-2*x) * B (z-1) ((m : ℤ)+x-s-a-1) +
          B (e+1) (s+a-2*x-1) * B (z-1) ((m : ℤ)+x-s-a))) := by
  let u := s+(a : ℤ)-2*x
  let y := (m : ℤ)+x-s-a
  have hA0 := discordant_estimator_sd_binom_omit_pred a x
  have hA1 := discordant_estimator_sd_binom_select_pred a x
  have hZ0 := discordant_estimator_sd_binom_omit_pred z y
  have hZ1 := discordant_estimator_sd_binom_select_pred z y
  have hD0 := discordant_estimator_sd_binom_select e u
  have hD1 := discordant_estimator_sd_binom_omit e (u-1)
  have ht : (x : ℝ)+(u : ℝ)+(y : ℝ) = m := by dsimp [u,y]; push_cast; ring
  have hn' : (a : ℝ)+(e+2)+z = 2*m := by exact_mod_cast hn
  change (m : ℝ) * (B a x * (B (e+2) u * B z y)) =
    (a : ℝ) * (B (a-1) x * (B (e+1) (u-1) * B z y) +
      B (a-1) (x-1) * (B (e+1) u * B z y)) +
    (2*(e+1) : ℝ) * (B a x * (B e (u-1) * B z y)) +
    (z : ℝ) * (B a x * (B (e+1) u * B (z-1) (y-1) + B (e+1) (u-1) * B (z-1) y))
  rw [show e+2 = (e+1)+1 by omega, discordant_estimator_sd_binom_pascal]
  push_cast at hD0 hD1
  linear_combination
    B (e+1) (u-1) * B z y * hA0 +
    B (e+1) u * B z y * hA1 +
    B a x * B (e+1) (u-1) * hZ0 +
    B a x * B (e+1) u * hZ1 +
    B a x * B z y * hD0 + B a x * B z y * hD1 +
    B a x * B z y * (B (e+1) (u-1) - B (e+1) u) * ht -
    B a x * B z y * B (e+1) (u-1) * hn'

lemma discordant_estimator_sd_partner11 (a e z m : ℕ) (s : ℤ) :
    (∑' x : ℤ, (a : ℝ) *
      (B (a-1) x * (B (e+1) (s+a-2*x-1) * B z ((m : ℤ)+x-s-a)) +
        B (a-1) (x-1) * (B (e+1) (s+a-2*x) * B z ((m : ℤ)+x-s-a)))) =
      (a : ℝ) * (C (a-1) (e+1) z ((m : ℤ)-1) s +
        C (a-1) (e+1) z ((m : ℤ)-1) (s-1)) := by
  by_cases ha : a = 0
  · simp [ha]
  have ha' : ((a-1 : ℕ) : ℤ) = (a : ℤ)-1 := by omega
  rw [tsum_mul_left,
    (discordant_estimator_sd_binom_summable (a-1) _).tsum_add
      (discordant_estimator_sd_binom_shift_summable (a-1) 1 _)]
  congr 1
  congr 1
  · apply tsum_congr
    intro x
    simp only [discordant_estimator_sd_count, ha']
    congr 2 <;> congr 1 <;> ring
  · let e' : ℤ ≃ ℤ := Equiv.subRight 1
    symm
    rw [discordant_estimator_sd_count, ← e'.tsum_eq]
    apply tsum_congr
    intro x
    change B (a-1) (x-1) * (B (e+1) (s-1+(a-1 : ℕ)-2*(x-1)) *
      B z ((m : ℤ)-1+(x-1)-(s-1)-(a-1 : ℕ))) =
      B (a-1) (x-1) * (B (e+1) (s+a-2*x) * B z ((m : ℤ)+x-s-a))
    simp only [ha']
    congr 2 <;> congr 1 <;> ring

lemma discordant_estimator_sd_partner00 (a e z m : ℕ) (s : ℤ) :
    (∑' x : ℤ, (z : ℝ) * (B a x *
      (B (e+1) (s+a-2*x) * B (z-1) ((m : ℤ)+x-s-a-1) +
        B (e+1) (s+a-2*x-1) * B (z-1) ((m : ℤ)+x-s-a)))) =
      (z : ℝ) * (C a (e+1) (z-1) ((m : ℤ)-1) s +
        C a (e+1) (z-1) ((m : ℤ)-1) (s-1)) := by
  rw [tsum_mul_left]
  simp_rw [mul_add]
  rw [(discordant_estimator_sd_binom_summable a _).tsum_add
    (discordant_estimator_sd_binom_summable a _)]
  rw [← mul_add]
  congr 1
  congr 1
  · apply tsum_congr
    intro x
    congr 2 <;> congr 1 <;> ring
  · apply tsum_congr
    intro x
    congr 2 <;> congr 1 <;> ring

lemma discordant_estimator_sd_partner_sum (a e z m : ℕ)
    (hn : a+(e+2)+z = 2*m) (s : ℤ) :
    (m : ℝ) * C a (e+2) z m s =
      (a : ℝ) * (C (a-1) (e+1) z ((m : ℤ)-1) s +
        C (a-1) (e+1) z ((m : ℤ)-1) (s-1)) +
      (2*(e+1) : ℝ) * C a e z ((m : ℤ)-1) (s-1) +
      (z : ℝ) * (C a (e+1) (z-1) ((m : ℤ)-1) s +
        C a (e+1) (z-1) ((m : ℤ)-1) (s-1)) := by
  let p := fun x : ℤ => (a : ℝ) *
    (B (a-1) x * (B (e+1) (s+a-2*x-1) * B z ((m : ℤ)+x-s-a)) +
      B (a-1) (x-1) * (B (e+1) (s+a-2*x) * B z ((m : ℤ)+x-s-a)))
  let q := fun x : ℤ => (2*(e+1) : ℝ) *
    (B a x * (B e (s+a-2*x-1) * B z ((m : ℤ)+x-s-a)))
  let r := fun x : ℤ => (z : ℝ) * (B a x *
    (B (e+1) (s+a-2*x) * B (z-1) ((m : ℤ)+x-s-a-1) +
      B (e+1) (s+a-2*x-1) * B (z-1) ((m : ℤ)+x-s-a)))
  have hp : Summable p :=
    ((discordant_estimator_sd_binom_summable (a-1) _).add
      (discordant_estimator_sd_binom_shift_summable (a-1) 1 _)).mul_left _
  have hq : Summable q := (discordant_estimator_sd_binom_summable a _).mul_left _
  have hr : Summable r := (discordant_estimator_sd_binom_summable a _).mul_left _
  calc
    (m : ℝ) * C a (e+2) z m s = ∑' x : ℤ,
        (m : ℝ) * (B a x * (B (e+2) (s+a-2*x) * B z ((m : ℤ)+x-s-a))) := by
      rw [tsum_mul_left]; rfl
    _ = ∑' x : ℤ, ((p x + q x) + r x) := by
      apply tsum_congr
      intro x
      exact discordant_estimator_sd_partner_term a e z m hn x s
    _ = (∑' x, p x) + (∑' x, q x) + ∑' x, r x := by
      rw [(hp.add hq).tsum_add hr, hp.tsum_add hq]
    _ = _ := by
      dsimp only [p,q,r]
      rw [discordant_estimator_sd_partner11, discordant_estimator_sd_partner00,
        tsum_mul_left]
      congr 2
      congr 1
      apply tsum_congr
      intro x
      congr 2 <;> congr 1 <;> ring

lemma discordant_estimator_sd_smooth_step (f : ℤ → ℝ) (c s : ℤ)
    (hf : SDShape f c) (hs : c+1 ≤ 2*s) :
    f (s+1) + f s ≤ f s + f (s-1) := by
  have h := (independent_convolution_shape f c hf).2 s (s+1) hs (by omega)
  simp only [smoothMass, show s+1-1 = s by ring] at h
  linarith

lemma discordant_estimator_sd_canonical_shape (a d z m : ℕ) (hm : 0 < m)
    (hn : a+d+z = 2*m) (hd : 1 ≤ d) : SDShape (C a d z m) d := by
  induction m using Nat.strong_induction_on generalizing a d z with
  | h m ih =>
    by_cases hd1 : d = 1
    · subst d
      exact discordant_estimator_sd_one_shape a z m hn
    by_cases hd2 : d = 2
    · subst d
      exact discordant_estimator_sd_two_shape a z m hn
    obtain ⟨e, rfl⟩ : ∃ e, d = e+2 := ⟨d-2, by omega⟩
    have he : 1 ≤ e := by omega
    have hm2 : 2 ≤ m := by omega
    have hcast : ((m-1 : ℕ) : ℤ) = (m : ℤ)-1 := by omega
    have hmid : SDShape (C a e z ((m : ℤ)-1)) e := by
      rw [← hcast]
      exact ih (m-1) (by omega) a e z (by omega) (by omega) he
    apply discordant_estimator_sd_shape_of_step
    · exact discordant_estimator_sd_count_symm a (e+2) z m hn
    · intro s hs
      have hA : (a : ℝ) *
          (C (a-1) (e+1) z ((m : ℤ)-1) (s+1) + C (a-1) (e+1) z ((m : ℤ)-1) s) ≤
          (a : ℝ) * (C (a-1) (e+1) z ((m : ℤ)-1) s + C (a-1) (e+1) z ((m : ℤ)-1) (s-1)) := by
        by_cases ha : a = 0
        · simp [ha]
        have hres : SDShape (C (a-1) (e+1) z ((m : ℤ)-1)) (e+1) := by
          rw [← hcast]
          exact ih (m-1) (by omega) (a-1) (e+1) z (by omega) (by omega) (by omega)
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg a)
        exact discordant_estimator_sd_smooth_step _ (e+1) s hres (by push_cast at hs ⊢; omega)
      have hZ : (z : ℝ) *
          (C a (e+1) (z-1) ((m : ℤ)-1) (s+1) + C a (e+1) (z-1) ((m : ℤ)-1) s) ≤
          (z : ℝ) * (C a (e+1) (z-1) ((m : ℤ)-1) s + C a (e+1) (z-1) ((m : ℤ)-1) (s-1)) := by
        by_cases hz : z = 0
        · simp [hz]
        have hres : SDShape (C a (e+1) (z-1) ((m : ℤ)-1)) (e+1) := by
          rw [← hcast]
          exact ih (m-1) (by omega) a (e+1) (z-1) (by omega) (by omega) (by omega)
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg z)
        exact discordant_estimator_sd_smooth_step _ (e+1) s hres (by push_cast at hs ⊢; omega)
      have hD : (2*(e+1) : ℝ) * C a e z ((m : ℤ)-1) s ≤
          (2*(e+1) : ℝ) * C a e z ((m : ℤ)-1) (s-1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hmid.2 (s-1) s (by push_cast at hs; omega) (by omega)
      have h := add_le_add (add_le_add hA hD) hZ
      have hnext := discordant_estimator_sd_partner_sum a e z m hn (s+1)
      simp only [show s+1-1 = s by ring] at hnext
      rw [← hnext,
        ← discordant_estimator_sd_partner_sum a e z m hn s] at h
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      nlinarith

lemma discordant_estimator_sd_real_range (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [List.sum_range_succ, Finset.sum_range_succ, ih]

lemma discordant_estimator_sd_binom_tsum_range (n : ℕ) (f : ℤ → ℝ) :
    (∑' k : ℤ, B n k * f k) = ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * f k := by
  rw [tsum_eq_sum (s := (Finset.range (n+1)).image (fun k : ℕ => (k : ℤ))) (by
    intro k hk
    by_cases h : 0 ≤ k ∧ k ≤ n
    · exfalso
      apply hk
      exact Finset.mem_image.mpr ⟨k.toNat, Finset.mem_range.mpr (by omega), by omega⟩
    · rw [discordant_estimator_sd_binom_zero _ _ (by omega), zero_mul])]
  rw [Finset.sum_image (by
    intro i hi j hj hij
    exact Int.ofNat_injective hij)]
  simp only [discordant_estimator_sd_binom_nat]

lemma discordant_estimator_sd_binom_truncate (n r : ℕ) (f : ℤ → ℝ)
    (hf : ∀ k : ℤ, (r : ℤ) < k → f k = 0) :
    (∑' k : ℤ, B n k * f k) =
      ((List.range (min n r+1)).map fun k => (n.choose k : ℝ) * f k).sum := by
  rw [discordant_estimator_sd_binom_tsum_range, discordant_estimator_sd_real_range]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkr
  have h : (r : ℤ) < k := by
    simp only [Finset.mem_range] at hk hkr
    omega
  rw [hf k h, mul_zero]

/-- A joint count sum. The last coordinate is forced by the treatment total. -/
noncomputable def discordant_estimator_sd_joint : List ℕ → ℤ → (List ℤ → ℝ) → ℝ
  | [], t, f => if t = 0 then f [] else 0
  | [n], t, f => B n t * f [t]
  | n :: n' :: ns, t, f =>
      ∑' x : ℤ, B n x * discordant_estimator_sd_joint (n' :: ns) (t-x) (fun xs => f (x::xs))

local notation "J" => discordant_estimator_sd_joint

lemma discordant_estimator_sd_joint_cons (n : ℕ) (ns : List ℕ) (t : ℤ) (f : List ℤ → ℝ) :
    J (n::ns) t f = ∑' x : ℤ, B n x * J ns (t-x) (fun xs => f (x::xs)) := by
  cases ns with
  | nil =>
    symm
    rw [tsum_eq_single t]
    · simp [discordant_estimator_sd_joint]
    · intro x hx
      simp [discordant_estimator_sd_joint, show t-x ≠ 0 by omega]
  | cons n' ns => rfl

lemma discordant_estimator_sd_joint_negative (ns : List ℕ) (t : ℤ) (f : List ℤ → ℝ)
    (ht : t < 0) : J ns t f = 0 := by
  induction ns generalizing t f with
  | nil => simp [discordant_estimator_sd_joint, show t ≠ 0 by omega]
  | cons n ns ih =>
    rw [discordant_estimator_sd_joint_cons]
    refine (tsum_congr (g := fun _ : ℤ => (0 : ℝ)) ?_).trans tsum_zero
    intro x
    by_cases hx : x < 0
    · rw [discordant_estimator_sd_binom_zero _ _ (Or.inl hx), zero_mul]
    · rw [ih (t-x) _ (by omega), mul_zero]

lemma discordant_estimator_sd_joint_cons_nat (n r : ℕ) (ns : List ℕ) (f : List ℤ → ℝ) :
    J (n::ns) r f = ((List.range (min n r+1)).map fun k =>
      (n.choose k : ℝ) * J ns (r-k : ℕ) (fun xs => f ((k : ℤ)::xs))).sum := by
  rw [discordant_estimator_sd_joint_cons,
    discordant_estimator_sd_binom_truncate n r _ (by
      intro k hk
      exact discordant_estimator_sd_joint_negative _ _ _ (by omega))]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  have hk' : k ≤ r := by
    have h := List.mem_range.mp hk
    omega
  rw [Nat.cast_sub hk']

lemma discordant_estimator_sd_binom_vandermonde (a b : ℕ) (t : ℤ) :
    (∑' x : ℤ, B a x * B b (t-x)) = B (a+b) t := by
  by_cases ht : t < 0
  · rw [discordant_estimator_sd_binom_zero _ _ (Or.inl ht)]
    refine (tsum_congr (g := fun _ : ℤ => (0 : ℝ)) ?_).trans tsum_zero
    intro x
    by_cases hx : x < 0
    · rw [discordant_estimator_sd_binom_zero _ _ (Or.inl hx), zero_mul]
    · rw [discordant_estimator_sd_binom_zero b (t-x) (Or.inl (by omega)), mul_zero]
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ t)
  rw [discordant_estimator_sd_binom_truncate a r _ (by
    intro k hk
    exact discordant_estimator_sd_binom_zero _ _ (Or.inl (by omega))),
    discordant_estimator_sd_binom_nat]
  have hfun : ((List.range (min a r+1)).map fun k =>
      (a.choose k : ℝ) * B b ((r : ℤ)-k)).sum =
      (((List.range (min a r+1)).map fun k => binomial a k * binomial b (r-k)).sum : ℕ) := by
    rw [Nat.cast_list_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    have hk' : k ≤ r := by have h := List.mem_range.mp hk; omega
    simp only [Function.comp_apply, Nat.cast_mul, binomial_eq_choose,
      ← Nat.cast_sub hk', discordant_estimator_sd_binom_nat]
  rw [hfun, bounded_vandermonde, binomial_eq_choose]

lemma discordant_estimator_sd_joint_canonical (a b c z m : ℕ) (s : ℤ) :
    J [a,b,c,z] m (fun xs => if 2*xs[0]!+xs[1]!+xs[2]!-(a : ℤ)-c = s then 1 else 0) =
      C a (b+c) z m (s+c) := by
  simp only [discordant_estimator_sd_joint, List.getElem!_cons_zero,
    List.getElem!_cons_succ, discordant_estimator_sd_count]
  apply tsum_congr
  intro x
  congr 1
  calc
    (∑' y : ℤ, B b y * ∑' w : ℤ,
        B c w * (B z ((m : ℤ)-x-y-w) *
          if 2*x+y+w-a-c = s then 1 else 0)) =
      ∑' y : ℤ, B b y * (B c (s+a+c-2*x-y) * B z ((m : ℤ)+x-s-a-c)) := by
        apply tsum_congr
        intro y
        congr 1
        rw [tsum_eq_single (s+a+c-2*x-y)]
        · rw [if_pos (by omega)]
          simp only [mul_one]
          rw [show (m : ℤ)-x-y-(s+a+c-2*x-y) = (m : ℤ)+x-s-a-c by ring]
        · intro w hw
          rw [if_neg (by omega)]
          ring
    _ = (∑' y : ℤ, B b y * B c ((s+c+a-2*x)-y)) * B z ((m : ℤ)+x-s-a-c) := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro y
      rw [show s+a+c-2*x-y = s+c+a-2*x-y by ring]
      ring
    _ = _ := by
      rw [discordant_estimator_sd_binom_vandermonde]
      rw [show (m : ℤ)+x-s-a-c = (m : ℤ)+x-(s+c)-a by ring]

lemma discordant_estimator_sd_flatMap_sum {A D : Type*} (xs : List A)
    (f : A → List D) (g : D → ℝ) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

lemma discordant_estimator_sd_filterMap_sum {A D : Type*} (xs : List A)
    (f : A → Option D) (g : D → ℝ) :
    ((xs.filterMap f).map g).sum =
      (xs.map fun x => match f x with | none => 0 | some y => g y).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : f x <;> simp [List.filterMap_cons, h, ih]

lemma discordant_estimator_sd_joint_design (v : Counts) (m : ℕ) (f : List ℤ → ℝ) :
    ((randomStates v m).map fun q => (multiplicity v q : ℝ) *
      f [q.a,q.b,q.c,q.d]).sum = J [v.a,v.b,v.c,v.d] m f := by
  have inner (a b : ℕ) :
      (((List.range (min v.c (m-a-b)+1)).filterMap fun c =>
        if m-a-b-c ≤ v.d then some (⟨a,b,c,m-a-b-c⟩ : Counts) else none).map
        fun q => (multiplicity v q : ℝ) * f [q.a,q.b,q.c,q.d]).sum =
      (binomial v.a a : ℝ) * (binomial v.b b : ℝ) *
        J [v.c,v.d] (m-a-b : ℕ) (fun xs => f ((a : ℤ)::(b : ℤ)::xs)) := by
    rw [discordant_estimator_sd_filterMap_sum,
      discordant_estimator_sd_joint_cons_nat, ← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    by_cases hd : m-a-b-c ≤ v.d
    · simp only [if_pos hd, multiplicity, Nat.cast_mul, discordant_estimator_sd_joint,
        discordant_estimator_sd_binom_nat, Function.comp_apply, binomial_eq_choose]
      ring
    · simp only [if_neg hd, discordant_estimator_sd_joint, discordant_estimator_sd_binom_nat,
        Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hd), zero_mul, mul_zero, Function.comp_apply]
      norm_num
  unfold randomStates
  simp only [discordant_estimator_sd_flatMap_sum, inner]
  rw [discordant_estimator_sd_joint_cons_nat]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [discordant_estimator_sd_joint_cons_nat, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp_apply, binomial_eq_choose]
  ring

/-- Exact integer statistic on every enumerated balanced state. -/
lemma discordant_estimator_sd_scaled_statistic (v : Counts) (m : ℕ) (hm : 0 < m)
    (hn : v.total = 2*m) (q : Counts) (hq : q ∈ randomStates v m) :
    (m : ℚ) * estimateQ (observed v q) =
      ((2*(q.a : ℤ)+q.b+q.c-v.a-v.c : ℤ) : ℚ) := by
  rcases random_state_facts v m q hq with ⟨ha,hb,hc,hd,ht⟩
  have hT : (observed v q).a + (observed v q).b = m := by
    dsimp [observed, Counts.total] at ht ⊢
    omega
  have hC : (observed v q).c + (observed v q).d = m := by
    dsimp [observed, Counts.total] at hn ht ⊢
    omega
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [estimateQ, ← Nat.cast_add, hT, hC]
  rw [mul_sub, mul_div_cancel₀ _ hmQ, mul_div_cancel₀ _ hmQ]
  have hcc : q.c ≤ v.a-q.a+v.c := by omega
  simp only [observed, Nat.cast_sub hcc, Nat.cast_add, Nat.cast_sub ha,
    Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  ring

lemma discordant_estimator_sd_mass_formula (v : Counts) (m : ℕ) (hm : 0 < m)
    (hn : v.total = 2*m) (s : ℤ) :
    scaledEstimatorMass v m s = C v.a (v.b+v.c) v.d m (s+v.c) / v.total.choose m := by
  unfold scaledEstimatorMass designProb
  congr 1
  calc
    _ = ((randomStates v m).map fun q => (multiplicity v q : ℝ) *
        (if 2*(q.a : ℤ)+q.b+q.c-v.a-v.c = s then 1 else 0)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro q hq
      dsimp only
      simp only [discordant_estimator_sd_scaled_statistic v m hm hn q hq, Int.cast_inj]
      split_ifs <;> ring
    _ = _ := by
      simpa only [List.getElem!_cons_zero, List.getElem!_cons_succ, Nat.cast_ofNat,
        Int.cast_ofNat] using
        (discordant_estimator_sd_joint_design v m
          (fun xs => if 2*xs[0]!+xs[1]!+xs[2]!-(v.a : ℤ)-v.c = s then 1 else 0)).trans
          (discordant_estimator_sd_joint_canonical v.a v.b v.c v.d m s)

lemma discordant_estimator_sd_finite_hasSum {A : Type*} (xs : List A)
    (g : A → ℤ) (w : A → ℝ) :
    HasSum (fun i : ℤ => (xs.map fun q => if g q = i then w q else 0).sum)
      (xs.map w).sum := by
  induction xs with
  | nil => simpa using (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℝ)) 0)
  | cons q xs ih =>
    simpa only [List.map_cons, List.sum_cons, eq_comm] using
      (hasSum_ite_eq (g q) (w q)).add ih

lemma discordant_estimator_sd_finite_mass {A : Type*} (xs : List A)
    (g : A → ℤ) (w : A → ℝ) (D : ℝ) (hD : 0 < D)
    (hw : ∀ q, 0 ≤ w q) (ht : (xs.map w).sum = D) :
    IsMass (fun i : ℤ => (xs.map fun q => if g q = i then w q else 0).sum / D) := by
  have hs := (discordant_estimator_sd_finite_hasSum xs g w).div_const D
  have hmoment : (fun i : ℤ => (i : ℝ) *
      (xs.map fun q => if g q = i then w q else 0).sum) =
      (fun i : ℤ => (xs.map fun q => if g q = i then (g q : ℝ)*w q else 0).sum) := by
    funext i
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    by_cases h : g q = i
    · simp [h]
    · simp [h]
  refine ⟨?_, hs.summable, ?_, ?_⟩
  · intro i
    apply div_nonneg _ hD.le
    apply List.sum_nonneg
    intro r hr
    rcases List.mem_map.mp hr with ⟨q,hq,rfl⟩
    split_ifs
    · exact hw q
    · exact le_rfl
  · rw [hs.tsum_eq, ht, div_self hD.ne']
  · have hm := (discordant_estimator_sd_finite_hasSum xs g
        (fun q => (g q : ℝ)*w q)).summable.div_const D
    apply hm.congr
    intro i
    rw [← mul_div_assoc, congrFun hmoment i]

lemma discordant_estimator_sd_mass_expansion (v : Counts) (m : ℕ) (hm : 0 < m)
    (hn : v.total = 2*m) :
    scaledEstimatorMass v m = fun s : ℤ =>
      ((randomStates v m).map fun q =>
        if 2*(q.a : ℤ)+q.b+q.c-v.a-v.c = s then (multiplicity v q : ℝ) else 0).sum /
        v.total.choose m := by
  funext s
  unfold scaledEstimatorMass designProb
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  dsimp only
  simp only [discordant_estimator_sd_scaled_statistic v m hm hn q hq, Int.cast_inj]

lemma discordant_estimator_sd_isMass (v : Counts) (m : ℕ) (hm : 0 < m)
    (hn : v.total = 2*m) : IsMass (scaledEstimatorMass v m) := by
  have hmn : m ≤ v.total := by omega
  have hD : (0 : ℝ) < v.total.choose m := by exact_mod_cast Nat.choose_pos hmn
  have ht : ((randomStates v m).map fun q => (multiplicity v q : ℝ)).sum =
      v.total.choose m := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (design_weight_total v m hmn)
    simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def] using h
  rw [discordant_estimator_sd_mass_expansion v m hm hn]
  exact discordant_estimator_sd_finite_mass (randomStates v m)
    (fun q => 2*(q.a : ℤ)+q.b+q.c-v.a-v.c)
    (fun q => (multiplicity v q : ℝ)) (v.total.choose m) hD (fun _ => Nat.cast_nonneg _) ht

lemma discordant_estimator_sd_mean_of_symmetry (f : ℤ → ℝ) (hf : IsMass f)
    (c : ℤ) (hsym : ∀ i, f (c-i) = f i) :
    (∑' i : ℤ, (i : ℝ)*f i) = (c : ℝ)/2 := by
  let e : ℤ ≃ ℤ := Equiv.subLeft c
  have he : (∑' i : ℤ, ((c-i : ℤ) : ℝ)*f (c-i)) = ∑' i : ℤ, (i : ℝ)*f i := by
    simpa [e] using e.tsum_eq (fun i : ℤ => (i : ℝ)*f i)
  have hfun : (fun i : ℤ => ((c-i : ℤ) : ℝ)*f (c-i)) =
      (fun i : ℤ => (c : ℝ)*f i - (i : ℝ)*f i) := by
    funext i
    rw [hsym]
    push_cast
    ring
  rw [hfun, (hf.2.1.mul_left (c : ℝ)).tsum_sub hf.2.2.2,
    tsum_mul_left, hf.2.2.1] at he
  linarith

/-- The full discordant-count hypothesis, with neither discordant coordinate
required to be individually positive. -/
theorem discordant_estimator_sd_proof (v : Counts) (m : ℕ) (hm : 0 < m)
    (hn : v.total = 2*m) (hd : 1 ≤ v.b+v.c) : IsSD (scaledEstimatorMass v m) := by
  have hmass := discordant_estimator_sd_isMass v m hm hn
  have hcan := discordant_estimator_sd_canonical_shape v.a (v.b+v.c) v.d m hm
    (by simpa only [Counts.total, Nat.add_assoc] using hn) hd
  have hmn : m ≤ v.total := by omega
  have hD : (0 : ℝ) < v.total.choose m := by exact_mod_cast Nat.choose_pos hmn
  have hshape : SDShape (scaledEstimatorMass v m) ((v.b : ℤ)-v.c) := by
    constructor
    · intro s
      rw [discordant_estimator_sd_mass_formula v m hm hn,
        discordant_estimator_sd_mass_formula v m hm hn]
      congr 1
      rw [show (v.b : ℤ)-v.c-s+v.c = ((v.b+v.c : ℕ) : ℤ)-(s+v.c) by push_cast; ring]
      exact hcan.1 (s+v.c)
    · intro i j hi hij
      rw [discordant_estimator_sd_mass_formula v m hm hn,
        discordant_estimator_sd_mass_formula v m hm hn]
      apply div_le_div_of_nonneg_right _ hD.le
      exact hcan.2 (i+v.c) (j+v.c) (by push_cast; omega) (by omega)
  exact ⟨hmass, (v.b : ℤ)-v.c,
    discordant_estimator_sd_mean_of_symmetry _ hmass _ hshape.1, hshape⟩

end AronowAudit.P003.Wave1
