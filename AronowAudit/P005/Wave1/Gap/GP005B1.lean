import AronowAudit.P005.P005_Formalization

namespace AronowAudit.P005.Wave1

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

/-!
The sampling identities include the second and third moments used by
the control-arm and treated-arm expectation formulas.
-/

lemma control_arm_expectation_add {n : ℕ} (s : ℕ)
    (f g : Finset (Fin n) → ℝ) :
    expectation s (fun S => f S + g S) = expectation s f + expectation s g := by
  simp only [expectation, Finset.sum_add_distrib, add_div]

lemma control_arm_expectation_sub {n : ℕ} (s : ℕ)
    (f g : Finset (Fin n) → ℝ) :
    expectation s (fun S => f S - g S) = expectation s f - expectation s g := by
  simp only [expectation, Finset.sum_sub_distrib, sub_div]

lemma control_arm_card {n s : ℕ} (S : Finset (Fin n)) (hS : S ∈ design n s) :
    S.card = s := (Finset.mem_powersetCard.mp hS).2

lemma control_arm_complement_card {n s : ℕ} (S : Finset (Fin n))
    (hS : S ∈ design n s) : (control S).card = n - s := by
  rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  simp only [Finset.card_univ, Fintype.card_fin, control_arm_card S hS]

lemma control_arm_complement_involution {n : ℕ} (S : Finset (Fin n)) :
    control (control S) = S := by
  ext i
  simp [control]

lemma control_arm_transport {n s : ℕ} (hsn : s ≤ n)
    (f : Finset (Fin n) → ℝ) :
    expectation s (fun S => f (control S)) = expectation (n - s) f := by
  classical
  have himage : (design n s).image control = design n (n - s) := by
    ext A
    constructor
    · intro hA
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hA
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, control_arm_complement_card S hS⟩
    · intro hA
      refine Finset.mem_image.mpr ⟨control A, ?_, control_arm_complement_involution A⟩
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [control_arm_complement_card A hA, Nat.sub_sub_self hsn]
  have hinj : Function.Injective (@control n) := by
    intro A B hAB
    simpa only [control_arm_complement_involution] using congrArg control hAB
  have hcard : (design n s).card = (design n (n - s)).card := by
    rw [← himage, Finset.card_image_of_injective _ hinj]
  unfold expectation
  rw [hcard, ← himage, Finset.sum_image]
  intro A hA B hB hAB
  exact hinj hAB

lemma control_arm_choose_step (n s : ℕ) (hn : 0 < n) (hs : 0 < s) :
    (n : ℝ) * ((n - 1).choose (s - 1) : ℝ) = (n.choose s : ℝ) * s := by
  have hh : n * (n - 1).choose (s - 1) = n.choose s * s := by
    simpa [Nat.sub_add_cancel (show 1 ≤ n by omega),
      Nat.sub_add_cancel (show 1 ≤ s by omega)] using
      Nat.add_one_mul_choose_eq (n - 1) (s - 1)
  exact_mod_cast hh

lemma control_arm_choose_two_ratio {n s : ℕ} (hn : 2 ≤ n) (hs : 2 ≤ s)
    (hsn : s ≤ n) :
    ((n - 2).choose (s - 2) : ℝ) / (n.choose s : ℝ) =
      (s : ℝ) * (s - 1) / ((n : ℝ) * (n - 1)) := by
  have h1 := control_arm_choose_step n s (by omega) (by omega)
  have h2 := control_arm_choose_step (n - 1) (s - 1) (by omega) (by omega)
  have hnn : n - 1 - 1 = n - 2 := by omega
  have hss : s - 1 - 1 = s - 2 := by omega
  rw [hnn, hss] at h2
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 1 ≤ s)] at h2
  norm_num only [Nat.cast_one] at h2
  have hp : (n : ℝ) * (n - 1) * ((n - 2).choose (s - 2) : ℝ) =
      (n.choose s : ℝ) * s * (s - 1) := by
    calc
      _ = (n : ℝ) * (((n - 1).choose (s - 1) : ℝ) * (s - 1)) := by rw [mul_assoc, h2]
      _ = _ := by rw [← mul_assoc, h1]
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have n1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have C0 : (n.choose s : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hsn).ne'
  field_simp [n0, n1, C0]
  nlinarith only [hp]

lemma control_arm_choose_three_ratio {n s : ℕ} (hn : 3 ≤ n) (hs : 3 ≤ s)
    (hsn : s ≤ n) :
    ((n - 3).choose (s - 3) : ℝ) / (n.choose s : ℝ) =
      (s : ℝ) * (s - 1) * (s - 2) / ((n : ℝ) * (n - 1) * (n - 2)) := by
  have h2 := control_arm_choose_two_ratio (n := n) (s := s) (by omega) (by omega) hsn
  have h3 := control_arm_choose_step (n - 2) (s - 2) (by omega) (by omega)
  have hnn : n - 2 - 1 = n - 3 := by omega
  have hss : s - 2 - 1 = s - 3 := by omega
  rw [hnn, hss] at h3
  rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 2 ≤ s)] at h3
  norm_num only [Nat.cast_ofNat] at h3
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have n1 : (n : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have n2 : (n : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have C0 : (n.choose s : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hsn).ne'
  have hp : (n : ℝ) * (n - 1) * ((n - 2).choose (s - 2) : ℝ) =
      (n.choose s : ℝ) * s * (s - 1) := by
    field_simp [n0, n1, C0] at h2
    nlinarith only [h2]
  have hp3 : (n : ℝ) * (n - 1) * (n - 2) * ((n - 3).choose (s - 3) : ℝ) =
      (n.choose s : ℝ) * s * (s - 1) * (s - 2) := by
    calc
      _ = (n : ℝ) * (n - 1) * (((n - 2).choose (s - 2) : ℝ) * (s - 2)) := by
        rw [mul_assoc, h3]
      _ = _ := by rw [← mul_assoc, hp]
  field_simp [n0, n1, n2, C0]
  nlinarith only [hp3]

lemma control_arm_impossible_inclusion {n s : ℕ} (R : Finset (Fin n)) (hR : s < R.card) :
    expectation s (fun S => if R ⊆ S then (1 : ℝ) else 0) = 0 := by
  have hz : ∀ S ∈ design n s, (if R ⊆ S then (1 : ℝ) else 0) = 0 := by
    intro S hS
    have hs := control_arm_card S hS
    have hnot : ¬R ⊆ S := by
      intro hsub
      have := Finset.card_le_card hsub
      omega
    simp only [if_neg hnot]
  rw [expectation_congr s _ (fun _ => 0) hz]
  simp only [expectation, Finset.sum_const_zero, zero_div]

lemma control_arm_pair_distinct {n s : ℕ} (hn : 3 ≤ n) (hs : 0 < s)
    (hsn : s ≤ n) (i j : Fin n) (hij : i ≠ j) :
    expectation s (fun S => indicator S i * indicator S j) =
      (s : ℝ) * (s - 1) / ((n : ℝ) * (n - 1)) := by
  classical
  have hcard : ({i, j} : Finset (Fin n)).card = 2 := by simp [hij]
  have hf : (fun S => indicator S i * indicator S j) =
      (fun S => if ({i, j} : Finset (Fin n)) ⊆ S then (1 : ℝ) else 0) := by
    funext S
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [indicator, Finset.insert_subset_iff, hi, hj]
  rw [hf]
  by_cases h2 : 2 ≤ s
  · rw [inclusion_count _ (by omega), hcard]
    exact control_arm_choose_two_ratio (by omega) h2 hsn
  · have hs1 : s = 1 := by omega
    rw [control_arm_impossible_inclusion _ (by omega), hs1]
    norm_num

lemma control_arm_triple_distinct {n s : ℕ} (hn : 3 ≤ n) (hs : 0 < s)
    (hsn : s ≤ n) (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    expectation s (fun S => indicator S i * indicator S j * indicator S k) =
      (s : ℝ) * (s - 1) * (s - 2) / ((n : ℝ) * (n - 1) * (n - 2)) := by
  classical
  have hcard : ({i, j, k} : Finset (Fin n)).card = 3 := by simp [hij, hik, hjk]
  have hf : (fun S => indicator S i * indicator S j * indicator S k) =
      (fun S => if ({i, j, k} : Finset (Fin n)) ⊆ S then (1 : ℝ) else 0) := by
    funext S
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> by_cases hk : k ∈ S <;>
      simp [indicator, Finset.insert_subset_iff, hi, hj, hk]
  rw [hf]
  by_cases h3 : 3 ≤ s
  · rw [inclusion_count _ (by omega), hcard]
    exact control_arm_choose_three_ratio hn h3 hsn
  · rw [control_arm_impossible_inclusion _ (by omega)]
    interval_cases s <;> norm_num at hs ⊢

lemma control_arm_pair_indicator {n s : ℕ} (hn : 3 ≤ n) (hs : 0 < s)
    (hsn : s ≤ n) (i j : Fin n) :
    expectation s (fun S => indicator S i * indicator S j) =
      (s : ℝ) * (s - 1) / ((n : ℝ) * (n - 1)) +
      if i = j then (s : ℝ) / n - (s : ℝ) * (s - 1) / ((n : ℝ) * (n - 1)) else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    have hf : (fun S => indicator S i * indicator S i) = (fun S => indicator S i) := by
      funext S
      by_cases hi : i ∈ S <;> simp [indicator, hi]
    rw [hf, indicator_expectation (by omega) hs hsn, if_pos rfl]
    ring
  · rw [control_arm_pair_distinct hn hs hsn i j hij, if_neg hij, add_zero]

lemma control_arm_triple_indicator {n s : ℕ} (hn : 3 ≤ n) (hs : 0 < s)
    (hsn : s ≤ n) (i j k : Fin n) :
    let p1 := (s : ℝ) / n
    let p2 := (s : ℝ) * (s - 1) / ((n : ℝ) * (n - 1))
    let p3 := (s : ℝ) * (s - 1) * (s - 2) / ((n : ℝ) * (n - 1) * (n - 2))
    expectation s (fun S => indicator S i * indicator S j * indicator S k) =
      p3 + (if i = j then p2 - p3 else 0) +
        (if i = k then p2 - p3 else 0) + (if j = k then p2 - p3 else 0) +
        (if i = j ∧ i = k then p1 - 3 * p2 + 2 * p3 else 0) := by
  classical
  dsimp only
  have hidem : ∀ S (a : Fin n), indicator S a * indicator S a = indicator S a := by
    intro S a
    by_cases ha : a ∈ S <;> simp [indicator, ha]
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp_rw [hidem]
      rw [indicator_expectation (by omega) hs hsn]
      simp only [ite_true, and_self]
      ring
    · simp_rw [hidem]
      rw [control_arm_pair_distinct hn hs hsn i k hik]
      simp only [ite_true, if_neg hik, true_and, add_zero]
      ring
  · by_cases hik : i = k
    · subst k
      have hf : (fun S => indicator S i * indicator S j * indicator S i) =
          (fun S => indicator S i * indicator S j) := by
        funext S
        calc
          _ = (indicator S i * indicator S i) * indicator S j := by ring
          _ = _ := by rw [hidem]
      rw [hf, control_arm_pair_distinct hn hs hsn i j hij]
      simp only [if_neg hij, ite_true, if_neg (Ne.symm hij), hij, false_and, ite_false, add_zero]
      ring
    · by_cases hjk : j = k
      · subst k
        have hf : (fun S => indicator S i * indicator S j * indicator S j) =
            (fun S => indicator S i * indicator S j) := by
          funext S
          rw [mul_assoc, hidem]
        rw [hf, control_arm_pair_distinct hn hs hsn i j hij]
        simp only [if_neg hij, ite_true, hij, hik, false_and, ite_false, add_zero]
        ring
      · rw [control_arm_triple_distinct hn hs hsn i j k hij hik hjk]
        simp only [if_neg hij, if_neg hik, if_neg hjk, hij, hik, false_and, ite_false, add_zero]

/-- Two arbitrary sample means: the constant and diagonal equality patterns. -/
lemma control_arm_mean_product {n s : ℕ} (hn : 3 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (a b : Fin n → ℝ) :
    expectation s (fun S => mean S a * mean S b) =
      ((s : ℝ) * (s - 1) / ((n : ℝ) * (n - 1)) * (∑ i, a i) * (∑ i, b i) +
       ((s : ℝ) / n - (s : ℝ) * (s - 1) / ((n : ℝ) * (n - 1))) *
         ∑ i, a i * b i) / (s : ℝ)^2 := by
  classical
  have hf : ∀ S ∈ design n s, mean S a * mean S b =
      (1 / (s : ℝ)^2) * ∑ i, ∑ j, (a i * b j) * (indicator S i * indicator S j) := by
    intro S hS
    have hsum : (∑ i, ∑ j, (a i * b j) * (indicator S i * indicator S j)) =
        (∑ i, indicator S i * a i) * (∑ j, indicator S j * b j) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum, indicator_sum S a, indicator_sum S b, mean, mean, control_arm_card S hS]
    ring
  rw [expectation_congr s _ _ hf, expectation_mul, expectation_sum]
  simp_rw [expectation_sum, expectation_mul, control_arm_pair_indicator hn hs hsn]
  have hterm : ∀ i j : Fin n,
      a i * b j * ((s : ℝ) * (s - 1) / ((n : ℝ) * (n - 1)) +
        if i = j then (s : ℝ) / n - (s : ℝ) * (s - 1) / ((n : ℝ) * (n - 1)) else 0) =
      ((s : ℝ) * (s - 1) / ((n : ℝ) * (n - 1))) * a i * b j +
        if i = j then (((s : ℝ) / n - (s : ℝ) * (s - 1) / ((n : ℝ) * (n - 1))) *
          a i * b j) else 0 := by
    intro i j
    by_cases hij : i = j <;> simp only [hij, ite_true, ite_false] <;> ring
  simp_rw [hterm, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma control_arm_centered_mean_product {n s : ℕ} (hn : 3 ≤ n) (hs : 0 < s)
    (hsn : s ≤ n) (a b : Fin n → ℝ) (ha : popMean a = 0) :
    expectation s (fun S => mean S a * mean S b) =
      ((n : ℝ) - s) / ((s : ℝ) * (n - 1)) * popMean (fun i => a i * b i) := by
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have s0 : (s : ℝ) ≠ 0 := by positivity
  have n1 : (n : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have ha0 : (∑ i, a i) = 0 := by
    have hh := ha
    simp only [popMean, mean, Finset.card_univ, Fintype.card_fin, div_eq_zero_iff, n0,
      or_false] at hh
    exact hh
  rw [control_arm_mean_product hn hs hsn a b, ha0]
  simp only [popMean, mean, Finset.card_univ, Fintype.card_fin]
  field_simp [n0, n1, s0]
  <;> ring

/-- A delta-pattern identity avoids enumerating the all-distinct triple sum. -/
lemma control_arm_triple_delta_sum {n : ℕ} (a b c : Fin n → ℝ)
    (ha : (∑ i, a i) = 0) (hb : (∑ i, b i) = 0) (hc : (∑ i, c i) = 0)
    (p1 p2 p3 : ℝ) :
    (∑ i, ∑ j, ∑ k, a i * b j * c k *
      (p3 + (if i = j then p2 - p3 else 0) +
        (if i = k then p2 - p3 else 0) + (if j = k then p2 - p3 else 0) +
        (if i = j ∧ i = k then p1 - 3 * p2 + 2 * p3 else 0))) =
      (p1 - 3 * p2 + 2 * p3) * ∑ i, a i * b i * c i := by
  classical
  have hexpand : ∀ i j k : Fin n,
      a i * b j * c k *
        (p3 + (if i = j then p2 - p3 else 0) +
          (if i = k then p2 - p3 else 0) + (if j = k then p2 - p3 else 0) +
          (if i = j ∧ i = k then p1 - 3 * p2 + 2 * p3 else 0)) =
      p3 * a i * b j * c k +
        (if i = j then (p2 - p3) * a i * b j * c k else 0) +
        (if i = k then (p2 - p3) * a i * b j * c k else 0) +
        (if j = k then (p2 - p3) * a i * b j * c k else 0) +
        (if i = j then if i = k then (p1 - 3 * p2 + 2 * p3) * a i * b j * c k else 0 else 0) := by
    intro i j k
    simp only [ite_and, mul_add, mul_ite, mul_zero]
    ring
  simp_rw [hexpand, Finset.sum_add_distrib]
  have h0 : (∑ i, ∑ j, ∑ k, p3 * a i * b j * c k) = 0 := by
    simp only [← Finset.mul_sum, hc, mul_zero, Finset.sum_const_zero]
  have h12 : (∑ i, ∑ j, ∑ k,
      if i = j then (p2 - p3) * a i * b j * c k else 0) = 0 := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, ← Finset.mul_sum, hc, mul_zero,
      Finset.sum_const_zero]
  have h13 : (∑ i, ∑ j, ∑ k,
      if i = k then (p2 - p3) * a i * b j * c k else 0) = 0 := by
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have he : ∀ i, (∑ j, (p2 - p3) * a i * b j * c i) = 0 := by
      intro i
      calc
        _ = (p2 - p3) * a i * (∑ j, b j) * c i := by rw [Finset.mul_sum, Finset.sum_mul]
        _ = 0 := by rw [hb]; ring
    simp_rw [he]
    exact Finset.sum_const_zero
  have h23 : (∑ i, ∑ j, ∑ k,
      if j = k then (p2 - p3) * a i * b j * c k else 0) = 0 := by
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    calc
      _ = (p2 - p3) * (∑ i, a i) * (∑ j, b j * c j) := by
        rw [mul_assoc, Finset.sum_mul_sum]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [ha]; ring
  have h123 : (∑ i, ∑ j, ∑ k,
      if i = j then if i = k then (p1 - 3 * p2 + 2 * p3) * a i * b j * c k else 0 else 0) =
      (p1 - 3 * p2 + 2 * p3) * ∑ i, a i * b i * c i := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [h0, h12, h13, h23, h123]
  ring

lemma control_arm_centered_triple {n s : ℕ} (hn : 3 ≤ n) (hs : 0 < s)
    (hsn : s ≤ n) (a b c : Fin n → ℝ)
    (ha : popMean a = 0) (hb : popMean b = 0) (hc : popMean c = 0) :
    expectation s (fun S => mean S a * mean S b * mean S c) =
      NTTT n s * popMean (fun i => a i * b i * c i) := by
  classical
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have s0 : (s : ℝ) ≠ 0 := by positivity
  have n1 : (n : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have n2 : (n : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hz : ∀ f : Fin n → ℝ, popMean f = 0 → (∑ i, f i) = 0 := by
    intro f hf
    simpa only [popMean, mean, Finset.card_univ, Fintype.card_fin,
      div_eq_zero_iff, n0, or_false] using hf
  have hf : ∀ S ∈ design n s, mean S a * mean S b * mean S c =
      (1 / (s : ℝ)^3) * ∑ i, ∑ j, ∑ k,
        (a i * b j * c k) * (indicator S i * indicator S j * indicator S k) := by
    intro S hS
    have hsum : (∑ i, ∑ j, ∑ k,
        (a i * b j * c k) * (indicator S i * indicator S j * indicator S k)) =
        (∑ i, indicator S i * a i) * (∑ j, indicator S j * b j) *
          (∑ k, indicator S k * c k) := by
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hsum, indicator_sum S a, indicator_sum S b, indicator_sum S c,
      mean, mean, mean, control_arm_card S hS]
    ring
  rw [expectation_congr s _ _ hf, expectation_mul, expectation_sum]
  simp_rw [expectation_sum, expectation_mul, control_arm_triple_indicator hn hs hsn]
  rw [control_arm_triple_delta_sum a b c (hz a ha) (hz b hb) (hz c hc)]
  simp only [NTTT, popMean, mean, Finset.card_univ, Fintype.card_fin]
  field_simp [n0, n1, n2, s0]
  <;> ring

lemma control_arm_pop_centered {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) :
    popMean (centered y) = 0 := by
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  change mean univ (fun i => y i - popMean y) = 0
  rw [mean_sub, mean_const univ hne]
  exact sub_self _

lemma control_arm_leverage_centered {n d : ℕ} (P : Population n d) (y : Fin n → ℝ) :
    (∑ k, popMean (fun i => P.x i k * P.x i k * centered y i)) = leverageCov P y := by
  have hsum : (∑ k, popMean (fun i => P.x i k * P.x i k * centered y i)) =
      popMean (fun i => leverage P i * centered y i) := by
    simp only [popMean, mean, leverage, dot, Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hsum]
  have hf : (fun i => leverage P i * centered y i) =
      (fun i => leverage P i * y i - popMean y * leverage P i) := by
    funext i
    dsimp [centered]
    ring
  rw [hf]
  simp only [popMean, mean_sub, mean_mul, leverageCov, popCov, sampleCov]
  ring

lemma control_arm_covariance_expectation {n s : ℕ} (hn : 3 ≤ n) (hs : 0 < s)
    (hsn : s ≤ n) (a b : Fin n → ℝ) :
    expectation s (fun S => sampleCov S a b) =
      ((s : ℝ) - 1) * n / ((s : ℝ) * (n - 1)) * popCov a b := by
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have s0 : (s : ℝ) ≠ 0 := by positivity
  have n1 : (n : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  change expectation s (fun S => mean S (fun i => a i * b i) - mean S a * mean S b) = _
  rw [control_arm_expectation_sub, mean_unbiased (by omega) hs hsn,
    control_arm_mean_product hn hs hsn]
  simp only [popCov, sampleCov, popMean, mean, Finset.card_univ, Fintype.card_fin]
  field_simp [n0, s0, n1]
  <;> ring

lemma control_arm_dot_armN_expectation {n d s : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hs : 0 < s) (hsn : s ≤ n) (hx : xMean P univ = 0)
    (y : Fin n → ℝ) :
    expectation s (fun S => dot (xMean P S) (armN P S y)) =
      (((n : ℝ) - s) / ((s : ℝ) * (n - 1)) - NTTT n s) * leverageCov P y := by
  classical
  have hxk : ∀ k, popMean (fun i => P.x i k) = 0 := by
    intro k
    exact congrFun hx k
  have hy : popMean (centered y) = 0 := control_arm_pop_centered (by omega) y
  have hf : ∀ S ∈ design n s, dot (xMean P S) (armN P S y) =
      (∑ k, mean S (fun i => P.x i k) * mean S (fun i => P.x i k * centered y i)) -
      (∑ k, mean S (fun i => P.x i k) * mean S (fun i => P.x i k) * mean S (centered y)) := by
    intro S hS
    have hne : S.Nonempty := Finset.card_pos.mp (by rw [control_arm_card S hS]; exact hs)
    have hN : ∀ k, armN P S y k = mean S (fun i => P.x i k * centered y i) -
        mean S (centered y) * mean S (fun i => P.x i k) := by
      intro k
      have hp : (fun i => P.x i k * centered y i) =
          (fun i => y i * P.x i k - popMean y * P.x i k) := by
        funext i
        dsimp [centered]
        ring
      rw [hp, mean_sub, mean_mul]
      change _ = _ - mean S (fun i => y i - popMean y) * _
      rw [mean_sub, mean_const S hne]
      dsimp [armN, xMean]
      ring
    simp only [dot, hN, xMean, mul_sub, Finset.sum_sub_distrib]
    apply congrArg₂ (fun a b : ℝ => a - b) rfl
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [expectation_congr s _ _ hf, control_arm_expectation_sub]
  simp_rw [expectation_sum,
    control_arm_centered_mean_product hn hs hsn _ _ (hxk _),
    control_arm_centered_triple hn hs hsn _ _ _ (hxk _) (hxk _) hy]
  have hprod : ∀ k, popMean (fun i => P.x i k * (P.x i k * centered y i)) =
      popMean (fun i => P.x i k * P.x i k * centered y i) := by
    intro k
    congr 1
    funext i
    ring
  simp_rw [hprod]
  rw [← Finset.mul_sum, ← Finset.mul_sum, control_arm_leverage_centered P y]
  ring

/-- Shared generic arm identity; only centering of x is used. This includes
singleton arms and does not divide by s-1. -/
lemma control_arm_generic_expectation {n d s : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hs : 0 < s) (hsn : s ≤ n) (hx : xMean P univ = 0)
    (y : Fin n → ℝ) (c : ℝ) :
    expectation s (fun S => mean S y - dot (xMean P S) (armN P S y) +
      c * sampleCov S (leverage P) y) =
    popMean y + (-((n : ℝ) - s) / ((s : ℝ) * (n - 1)) + NTTT n s +
      c * ((s : ℝ) - 1) * n / ((s : ℝ) * (n - 1))) * leverageCov P y := by
  rw [control_arm_expectation_add, control_arm_expectation_sub,
    mean_unbiased (by omega) hs hsn, control_arm_dot_armN_expectation P hn hs hsn hx y,
    expectation_mul, control_arm_covariance_expectation hn hs hsn]
  change _ = _ + _ * popCov (leverage P) y
  dsimp only [leverageCov]
  ring

lemma control_arm_coefficient_factor {n s : ℕ} (hn : 3 ≤ n) (hs : 0 < s) (c : ℝ) :
    -((n : ℝ) - s) / ((s : ℝ) * (n - 1)) + NTTT n s +
      c * ((s : ℝ) - 1) * n / ((s : ℝ) * (n - 1)) =
    (c - ((n : ℝ) - s) / ((n - 2 : ℝ) * s)) *
      (((s : ℝ) - 1) * n / ((s : ℝ) * (n - 1))) := by
  have n1 : (n : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have n2 : (n : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have s0 : (s : ℝ) ≠ 0 := by positivity
  dsimp only [NTTT]
  field_simp [n1, n2, s0]
  <;> ring

lemma control_arm_coefficient_unique {n s : ℕ} (hn : 3 ≤ n) (hs : 2 ≤ s) (c : ℝ) :
    (-((n : ℝ) - s) / ((s : ℝ) * (n - 1)) + NTTT n s +
      c * ((s : ℝ) - 1) * n / ((s : ℝ) * (n - 1)) = 0 ↔
      c = ((n : ℝ) - s) / ((n - 2 : ℝ) * s)) := by
  rw [control_arm_coefficient_factor hn (by omega) c]
  have hb : (((s : ℝ) - 1) * n / ((s : ℝ) * (n - 1))) ≠ 0 := by
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
    apply ne_of_gt
    exact div_pos (mul_pos (by linarith) (by linarith)) (mul_pos (by linarith) (by linarith))
  rw [mul_eq_zero, or_iff_left hb, sub_eq_zero]

lemma control_arm_unbiased_any_size {n d s : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hs : 0 < s) (hsn : s ≤ n) (hx : xMean P univ = 0)
    (y : Fin n → ℝ) : expectation s (fun S => armDebiased P S y) = popMean y := by
  have hf : ∀ S ∈ design n s, armDebiased P S y =
      mean S y - dot (xMean P S) (armN P S y) +
        (((n : ℝ) - s) / ((n - 2 : ℝ) * s)) * sampleCov S (leverage P) y := by
    intro S hS
    simp only [armDebiased, control_arm_card S hS]
  rw [expectation_congr s _ _ hf,
    control_arm_generic_expectation P hn hs hsn hx y,
    control_arm_coefficient_factor hn hs]
  simp only [sub_self, zero_mul, add_zero]

/-- The control-arm expectation, unique debiasing coefficient and unbiasedness. -/
theorem control_arm_expectation_proof {n d m : ℕ} (P : Population n d) (hn : 3 ≤ n)
    (hm : 0 < m) (hmn : m < n) (hc : 2 ≤ n-m) (hx : xMean P univ = 0) (c : ℝ) :
    expectation m (fun S => mean (control S) P.yC -
      dot (xMean P (control S)) (armN P (control S) P.yC) +
      c*sampleCov (control S) (leverage P) P.yC) =
        popMean P.yC + (-(m : ℝ)/(((n : ℝ)-m)*(n-1)) + NCCC n m +
          c*((n : ℝ)-m-1)*n/(((n : ℝ)-m)*(n-1))) * leverageCov P P.yC ∧
    (-(m : ℝ)/(((n : ℝ)-m)*(n-1)) + NCCC n m +
       c*((n : ℝ)-m-1)*n/(((n : ℝ)-m)*(n-1)) = 0 ↔
      c = (m : ℝ)/((n-2 : ℝ)*(n-m))) ∧
    expectation m (fun S => armDebiased P (control S) P.yC) = popMean P.yC := by
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := Nat.cast_sub (le_of_lt hmn)
  have hs : 0 < n - m := Nat.sub_pos_of_lt hmn
  have he := control_arm_generic_expectation P hn hs (Nat.sub_le n m) hx P.yC c
  have hu := control_arm_coefficient_unique hn hc c
  have hz := control_arm_unbiased_any_size P hn hs (Nat.sub_le n m) hx P.yC
  have hmirror : (n : ℝ) - ((n : ℝ) - m) = m := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [control_arm_transport (le_of_lt hmn) (fun S => mean S P.yC - dot (xMean P S) (armN P S P.yC) + c * sampleCov S (leverage P) P.yC)]
    simpa only [hcast, hmirror, NCCC] using he
  · simpa only [hcast, hmirror, NCCC] using hu
  · rw [control_arm_transport (le_of_lt hmn) (fun S => armDebiased P S P.yC)]
    exact hz

/-- The treated-arm expectation, debiasing coefficient and unbiasedness. -/
theorem treated_arm_expectation_proof {n d m : ℕ} (P : Population n d) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hmn : m < n) (hx : xMean P univ = 0) (c : ℝ) :
    expectation m (fun S => mean S P.yT - dot (xMean P S) (armN P S P.yT) +
      c*sampleCov S (leverage P) P.yT) =
        popMean P.yT + (-((n : ℝ)-m)/((m : ℝ)*(n-1)) + NTTT n m +
          c*((m : ℝ)-1)*n/((m : ℝ)*(n-1))) * leverageCov P P.yT ∧
    (-((n : ℝ)-m)/((m : ℝ)*(n-1)) + NTTT n m +
       c*((m : ℝ)-1)*n/((m : ℝ)*(n-1)) = 0 ↔
      c = ((n : ℝ)-m)/((n-2 : ℝ)*m)) ∧
    expectation m (fun S => armDebiased P S P.yT) = popMean P.yT ∧
    expectation m (fun S => mean S P.yT-dot (xMean P S) (armN P S P.yT) +
      (m : ℝ)/((n-2 : ℝ)*(n-m))*sampleCov S (leverage P) P.yT) =
      popMean P.yT + ((m : ℝ)^2-((n : ℝ)-m)^2)/((n-2 : ℝ)*m*(n-m)) *
        (((m : ℝ)-1)*n/((m : ℝ)*(n-1))) * leverageCov P P.yT := by
  have hs : 0 < m := by omega
  have hmn' : m ≤ n := le_of_lt hmn
  have hfirst := control_arm_generic_expectation P hn hs hmn' hx P.yT c
  have hsecond := control_arm_coefficient_unique hn hm c
  have hthird := control_arm_unbiased_any_size P hn hs hmn' hx P.yT
  refine ⟨hfirst, hsecond, hthird, ?_⟩
  rw [control_arm_generic_expectation P hn hs hmn' hx P.yT,
    control_arm_coefficient_factor hn hs]
  have n2 : (n - 2 : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have m0 : (m : ℝ) ≠ 0 := by positivity
  have nm0 : (n - m : ℝ) ≠ 0 := by
    have : (m : ℝ) < n := by exact_mod_cast hmn
    linarith
  have hweight : (m : ℝ) / ((n - 2 : ℝ) * (n - m)) -
      ((n : ℝ) - m) / ((n - 2 : ℝ) * m) =
      ((m : ℝ)^2 - ((n : ℝ) - m)^2) / ((n - 2 : ℝ) * m * (n - m)) := by
    field_simp [n2, m0, nm0]
    <;> ring
  rw [hweight]

end
end AronowAudit.P005.Wave1
