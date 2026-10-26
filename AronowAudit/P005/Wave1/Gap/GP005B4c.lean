import AronowAudit.P005.Wave1.Gap.GP005B4b
import AronowAudit.P005.Wave1.Gap.GP005B1

namespace AronowAudit.P005.Wave1

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
attribute [local instance] Classical.propDecidable

lemma GP005B4c_choose_four {n s : ℕ} (hn : 4 ≤ n) (hs : 4 ≤ s) (hsn : s ≤ n) :
    ((n-4).choose (s-4) : ℝ) / (n.choose s : ℝ) =
      (s : ℝ)*(s-1)*(s-2)*(s-3)/((n : ℝ)*(n-1)*(n-2)*(n-3)) := by
  have h3 := control_arm_choose_three_ratio (n := n) (s := s) (by omega) (by omega) hsn
  have h4 := control_arm_choose_step (n-3) (s-3) (by omega) (by omega)
  rw [show n-3-1 = n-4 by omega, show s-3-1 = s-4 by omega] at h4
  rw [Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 3 ≤ s)] at h4
  norm_num only [Nat.cast_ofNat] at h4
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have n0 : (n : ℝ) ≠ 0 := by linarith
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  have n2 : (n : ℝ)-2 ≠ 0 := by linarith
  have n3 : (n : ℝ)-3 ≠ 0 := by linarith
  have C0 : (n.choose s : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hsn).ne'
  have hp : (n : ℝ)*(n-1)*(n-2)*((n-3).choose (s-3) : ℝ) =
      (n.choose s : ℝ)*s*(s-1)*(s-2) := by
    field_simp [n0, n1, n2, C0] at h3
    nlinarith only [h3]
  have hp4 : (n : ℝ)*(n-1)*(n-2)*(n-3)*((n-4).choose (s-4) : ℝ) =
      (n.choose s : ℝ)*s*(s-1)*(s-2)*(s-3) := by
    calc
      _ = (n : ℝ)*(n-1)*(n-2)*(((n-3).choose (s-3) : ℝ)*(s-3)) := by
        rw [mul_assoc, h4]
      _ = _ := by rw [← mul_assoc, hp]
  field_simp [n0, n1, n2, n3, C0]
  nlinarith only [hp4]

lemma GP005B4c_inclusion_small {n s : ℕ} (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (R : Finset (Fin n)) (hpos : 0 < R.card) (hfour : R.card ≤ 4) :
    expectation s (fun S => if R ⊆ S then (1 : ℝ) else 0) =
      if R.card = 1 then (s : ℝ)/n else
      if R.card = 2 then (s : ℝ)*(s-1)/((n : ℝ)*(n-1)) else
      if R.card = 3 then (s : ℝ)*(s-1)*(s-2)/((n : ℝ)*(n-1)*(n-2)) else
        (s : ℝ)*(s-1)*(s-2)*(s-3)/((n : ℝ)*(n-1)*(n-2)*(n-3)) := by
  have hr : R.card = 1 ∨ R.card = 2 ∨ R.card = 3 ∨ R.card = 4 := by omega
  rcases hr with hr | hr | hr | hr
  · rw [inclusion_count R (by omega), hr]
    simp only [ite_true]
    have h := control_arm_choose_step n s (by omega) hs
    have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have C0 : (n.choose s : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hsn).ne'
    field_simp [n0, C0]
    nlinarith only [h]
  · simp only [hr, show (2 : ℕ) ≠ 1 by decide, ite_false, ite_true]
    by_cases hks : 2 ≤ s
    · rw [inclusion_count R (by omega), hr]
      exact control_arm_choose_two_ratio (by omega) hks hsn
    · rw [control_arm_impossible_inclusion R (by omega)]
      interval_cases s <;> norm_num at hs ⊢
  · simp only [hr, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ite_false, ite_true]
    by_cases hks : 3 ≤ s
    · rw [inclusion_count R (by omega), hr]
      exact control_arm_choose_three_ratio (by omega) hks hsn
    · rw [control_arm_impossible_inclusion R (by omega)]
      interval_cases s <;> norm_num at hs ⊢
  · simp only [hr, show (4 : ℕ) ≠ 1 by decide, show (4 : ℕ) ≠ 2 by decide, show (4 : ℕ) ≠ 3 by decide, ite_false, ite_true]
    by_cases hks : 4 ≤ s
    · rw [inclusion_count R (by omega), hr]
      exact GP005B4c_choose_four (by omega) hks hsn
    · rw [control_arm_impossible_inclusion R (by omega)]
      interval_cases s <;> norm_num at hs ⊢

/-- The fifteen equality patterns of four labelled inclusion indicators. -/
lemma GP005B4c_four_indicator {n s : ℕ} (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (i j k l : Fin n) :
    let p1 := (s : ℝ)/n
    let p2 := (s : ℝ)*(s-1)/((n : ℝ)*(n-1))
    let p3 := (s : ℝ)*(s-1)*(s-2)/((n : ℝ)*(n-1)*(n-2))
    let p4 := (s : ℝ)*(s-1)*(s-2)*(s-3)/((n : ℝ)*(n-1)*(n-2)*(n-3))
    expectation s (fun S => indicator S i * indicator S j * indicator S k * indicator S l) =
      p4 +
      (if i=j then p3-p4 else 0) + (if i=k then p3-p4 else 0) +
      (if i=l then p3-p4 else 0) + (if j=k then p3-p4 else 0) +
      (if j=l then p3-p4 else 0) + (if k=l then p3-p4 else 0) +
      (if i=j ∧ i=k then p2-3*p3+2*p4 else 0) +
      (if i=j ∧ i=l then p2-3*p3+2*p4 else 0) +
      (if i=k ∧ i=l then p2-3*p3+2*p4 else 0) +
      (if j=k ∧ j=l then p2-3*p3+2*p4 else 0) +
      (if i=j ∧ k=l then p2-2*p3+p4 else 0) +
      (if i=k ∧ j=l then p2-2*p3+p4 else 0) +
      (if i=l ∧ j=k then p2-2*p3+p4 else 0) +
      (if i=j ∧ i=k ∧ i=l then p1-7*p2+12*p3-6*p4 else 0) := by
  dsimp only
  have hf : (fun S => indicator S i * indicator S j * indicator S k * indicator S l) =
      (fun S => if ({i,j,k,l} : Finset (Fin n)) ⊆ S then (1 : ℝ) else 0) := by
    funext S
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      by_cases hk : k ∈ S <;> by_cases hl : l ∈ S <;> simp [indicator, Finset.insert_subset_iff, hi, hj, hk, hl]
  have hp : 0 < ({i,j,k,l} : Finset (Fin n)).card := Finset.card_pos.mpr (by simp)
  have h4 : ({i,j,k,l} : Finset (Fin n)).card ≤ 4 := by
    have := Finset.card_insert_le i ({j,k,l} : Finset (Fin n))
    have := Finset.card_insert_le j ({k,l} : Finset (Fin n))
    have := Finset.card_insert_le k ({l} : Finset (Fin n))
    simp only [Finset.card_singleton] at *
    omega
  rw [hf, GP005B4c_inclusion_small hn hs hsn _ hp h4]
  by_cases hij : i=j <;> by_cases hik : i=k <;> by_cases hil : i=l <;>
    by_cases hjk : j=k <;> by_cases hjl : j=l <;> by_cases hkl : k=l <;>
    simp_all <;> ring

lemma GP005B4c_four_delta_sum {n : ℕ} (a b c d : Fin n → ℝ)
    (ha : (∑ i, a i)=0) (hb : (∑ i, b i)=0)
    (hc : (∑ i, c i)=0) (hd : (∑ i, d i)=0) (p1 p2 p3 p4 : ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, a i*b j*c k*d l*(
      p4 + (if i=j then p3-p4 else 0) + (if i=k then p3-p4 else 0) + (if i=l then p3-p4 else 0) + (if j=k then p3-p4 else 0) + (if j=l then p3-p4 else 0) + (if k=l then p3-p4 else 0) + (if i=j ∧ i=k then p2-3*p3+2*p4 else 0) + (if i=j ∧ i=l then p2-3*p3+2*p4 else 0) + (if i=k ∧ i=l then p2-3*p3+2*p4 else 0) + (if j=k ∧ j=l then p2-3*p3+2*p4 else 0) + (if i=j ∧ k=l then p2-2*p3+p4 else 0) + (if i=k ∧ j=l then p2-2*p3+p4 else 0) + (if i=l ∧ j=k then p2-2*p3+p4 else 0) + (if i=j ∧ i=k ∧ i=l then p1-7*p2+12*p3-6*p4 else 0))) =
      (p2-2*p3+p4)*((∑ i, a i*b i)*(∑ i, c i*d i) +
        (∑ i, a i*c i)*(∑ i, b i*d i) + (∑ i, a i*d i)*(∑ i, b i*c i)) +
      (p1-7*p2+12*p3-6*p4)*(∑ i, a i*b i*c i*d i) := by
  have hexpand : ∀ i j k l : Fin n,
      a i*b j*c k*d l*(p4 + (if i=j then p3-p4 else 0) + (if i=k then p3-p4 else 0) + (if i=l then p3-p4 else 0) + (if j=k then p3-p4 else 0) + (if j=l then p3-p4 else 0) + (if k=l then p3-p4 else 0) + (if i=j ∧ i=k then p2-3*p3+2*p4 else 0) + (if i=j ∧ i=l then p2-3*p3+2*p4 else 0) + (if i=k ∧ i=l then p2-3*p3+2*p4 else 0) + (if j=k ∧ j=l then p2-3*p3+2*p4 else 0) + (if i=j ∧ k=l then p2-2*p3+p4 else 0) + (if i=k ∧ j=l then p2-2*p3+p4 else 0) + (if i=l ∧ j=k then p2-2*p3+p4 else 0) + (if i=j ∧ i=k ∧ i=l then p1-7*p2+12*p3-6*p4 else 0)) =
      p4*a i*b j*c k*d l +
      (if i=j then (p3-p4)*a i*b j*c k*d l else 0) +
      (if i=k then (p3-p4)*a i*b j*c k*d l else 0) +
      (if i=l then (p3-p4)*a i*b j*c k*d l else 0) +
      (if j=k then (p3-p4)*a i*b j*c k*d l else 0) +
      (if j=l then (p3-p4)*a i*b j*c k*d l else 0) +
      (if k=l then (p3-p4)*a i*b j*c k*d l else 0) +
      (if i=j ∧ i=k then (p2-3*p3+2*p4)*a i*b j*c k*d l else 0) +
      (if i=j ∧ i=l then (p2-3*p3+2*p4)*a i*b j*c k*d l else 0) +
      (if i=k ∧ i=l then (p2-3*p3+2*p4)*a i*b j*c k*d l else 0) +
      (if j=k ∧ j=l then (p2-3*p3+2*p4)*a i*b j*c k*d l else 0) +
      (if i=j ∧ k=l then (p2-2*p3+p4)*a i*b j*c k*d l else 0) +
      (if i=k ∧ j=l then (p2-2*p3+p4)*a i*b j*c k*d l else 0) +
      (if i=l ∧ j=k then (p2-2*p3+p4)*a i*b j*c k*d l else 0) +
      (if i=j ∧ i=k ∧ i=l then (p1-7*p2+12*p3-6*p4)*a i*b j*c k*d l else 0) := by
    intro i j k l
    simp only [mul_add, mul_ite, mul_zero, ite_and]
    ring
  simp_rw [hexpand, Finset.sum_add_distrib]
  have h0 : (∑ i, ∑ j, ∑ k, ∑ l, p4*a i*b j*c k*d l) = 0 := by
    try simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ha, hb, hc, hd,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l, if i=j then (p3-p4)*a i*b j*c k*d l else 0) = 0 := by
    try simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ha, hb, hc, hd,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h2 : (∑ i, ∑ j, ∑ k, ∑ l, if i=k then (p3-p4)*a i*b j*c k*d l else 0) = 0 := by
    try simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ha, hb, hc, hd,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h3 : (∑ i, ∑ j, ∑ k, ∑ l, if i=l then (p3-p4)*a i*b j*c k*d l else 0) = 0 := by
    try simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ha, hb, hc, hd,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h4 : (∑ i, ∑ j, ∑ k, ∑ l, if j=k then (p3-p4)*a i*b j*c k*d l else 0) = 0 := by
    try simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ha, hb, hc, hd,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h5 : (∑ i, ∑ j, ∑ k, ∑ l, if j=l then (p3-p4)*a i*b j*c k*d l else 0) = 0 := by
    try simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ha, hb, hc, hd,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h6 : (∑ i, ∑ j, ∑ k, ∑ l, if k=l then (p3-p4)*a i*b j*c k*d l else 0) = 0 := by
    try simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ha, hb, hc, hd,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h7 : (∑ i, ∑ j, ∑ k, ∑ l, if i=j ∧ i=k then (p2-3*p3+2*p4)*a i*b j*c k*d l else 0) = 0 := by
    try simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ha, hb, hc, hd,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h8 : (∑ i, ∑ j, ∑ k, ∑ l, if i=j ∧ i=l then (p2-3*p3+2*p4)*a i*b j*c k*d l else 0) = 0 := by
    try simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ha, hb, hc, hd,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h9 : (∑ i, ∑ j, ∑ k, ∑ l, if i=k ∧ i=l then (p2-3*p3+2*p4)*a i*b j*c k*d l else 0) = 0 := by
    try simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ha, hb, hc, hd,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h10 : (∑ i, ∑ j, ∑ k, ∑ l, if j=k ∧ j=l then (p2-3*p3+2*p4)*a i*b j*c k*d l else 0) = 0 := by
    try simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ha, hb, hc, hd,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h11 : (∑ i, ∑ j, ∑ k, ∑ l, if i=j ∧ k=l then (p2-2*p3+p4)*a i*b j*c k*d l else 0) = (p2-2*p3+p4)*(∑ i, a i*b i)*(∑ i, c i*d i) := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    calc
      _ = ∑ i, ∑ j, (p2-2*p3+p4)*(a i*b i)*(c j*d j) := by
        repeat' (apply Finset.sum_congr rfl; intro _ _)
        ring
      _ = _ := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have h12 : (∑ i, ∑ j, ∑ k, ∑ l, if i=k ∧ j=l then (p2-2*p3+p4)*a i*b j*c k*d l else 0) = (p2-2*p3+p4)*(∑ i, a i*c i)*(∑ i, b i*d i) := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    calc
      _ = ∑ i, ∑ j, (p2-2*p3+p4)*(a i*c i)*(b j*d j) := by
        repeat' (apply Finset.sum_congr rfl; intro _ _)
        ring
      _ = _ := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have h13 : (∑ i, ∑ j, ∑ k, ∑ l, if i=l ∧ j=k then (p2-2*p3+p4)*a i*b j*c k*d l else 0) = (p2-2*p3+p4)*(∑ i, a i*d i)*(∑ i, b i*c i) := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    calc
      _ = ∑ i, ∑ j, (p2-2*p3+p4)*(a i*d i)*(b j*c j) := by
        repeat' (apply Finset.sum_congr rfl; intro _ _)
        ring
      _ = _ := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have h14 : (∑ i, ∑ j, ∑ k, ∑ l, if i=j ∧ i=k ∧ i=l then (p1-7*p2+12*p3-6*p4)*a i*b j*c k*d l else 0) = (p1-7*p2+12*p3-6*p4)*(∑ i, a i*b i*c i*d i) := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [Finset.sum_mul, Finset.mul_sum]
    repeat' (apply Finset.sum_congr rfl; intro _ _) 
    ring
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  ring

/-- Scalar comparison used after the fourth-moment equality. -/
lemma GP005B4c_four_comparison (N A C X Z D : ℝ)
    (hN : 4 ≤ N) (hA : 0 ≤ A) (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hZ : Z ≤ X) (hD : D ≤ X) (hZD : Z ≤ N*D)
    (hAC : A ≤ C) (h3 : 3*(N-2)*A ≤ (N-1)*C) :
    A*(X+2*Z)+(C-6*A)*D ≤ C*X := by
  by_cases hB : 0 ≤ C-6*A
  · have h1 := mul_le_mul_of_nonneg_left hZ (by positivity : 0 ≤ 2*A)
    have h2 := mul_le_mul_of_nonneg_left hD hB
    have h3 := mul_nonneg hA hX
    nlinarith
  · have hB' : C-6*A ≤ 0 := le_of_not_ge hB
    have h1 := mul_le_mul_of_nonpos_left hZD hB'
    have hK : 0 ≤ 2*N*A+C-6*A := by
      have := mul_nonneg (by linarith : 0 ≤ 2*N-6) hA
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left hZ hK
    have h3' := mul_le_mul_of_nonneg_right h3 hX
    nlinarith

lemma GP005B4c_four_moment {n s : ℕ} (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (u v : Fin n → ℝ) (hu : (∑ i, u i)=0) (hv : (∑ i, v i)=0) :
    let p1 := (s : ℝ)/n
    let p2 := (s : ℝ)*(s-1)/((n : ℝ)*(n-1))
    let p3 := (s : ℝ)*(s-1)*(s-2)/((n : ℝ)*(n-1)*(n-2))
    let p4 := (s : ℝ)*(s-1)*(s-2)*(s-3)/((n : ℝ)*(n-1)*(n-2)*(n-3))
    expectation s (fun S => (mean S u * mean S v)^2) =
      ((p2-2*p3+p4)*((∑ i, u i^2)*(∑ i, v i^2)+2*(∑ i, u i*v i)^2) +
        (p1-7*p2+12*p3-6*p4)*(∑ i, u i^2*v i^2))/(s : ℝ)^4 := by
  dsimp only
  have hf : ∀ S ∈ design n s, (mean S u*mean S v)^2 =
      (1/(s : ℝ)^4) * ∑ i, ∑ j, ∑ k, ∑ l,
        (u i*v j*u k*v l)*(indicator S i*indicator S j*indicator S k*indicator S l) := by
    intro S hS
    have hsum : (∑ i, ∑ j, ∑ k, ∑ l,
        (u i*v j*u k*v l)*(indicator S i*indicator S j*indicator S k*indicator S l)) =
        (∑ i, indicator S i*u i)*(∑ j, indicator S j*v j)*
          (∑ k, indicator S k*u k)*(∑ l, indicator S l*v l) := by
      calc
        _ = ∑ i, ∑ j, ∑ k, ∑ l,
            (indicator S i*u i)*(indicator S j*v j)*(indicator S k*u k)*(indicator S l*v l) := by
          repeat' (apply Finset.sum_congr rfl; intro _ _)
          ring
        _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]
    rw [hsum, indicator_sum, indicator_sum, mean, mean, control_arm_card S hS]
    ring
  rw [expectation_congr s _ _ hf, expectation_mul, expectation_sum]
  simp_rw [expectation_sum, expectation_mul, GP005B4c_four_indicator hn hs hsn]
  rw [GP005B4c_four_delta_sum u v u v hu hv hu hv]
  simp only [← pow_two]
  have hvu : (∑ i, v i*u i) = ∑ i, u i*v i := by apply Finset.sum_congr rfl; intros; ring
  rw [hvu]
  have huv : (∑ i, u i*v i*u i*v i) = ∑ i, u i^2*v i^2 := by
    apply Finset.sum_congr rfl; intros; ring
  rw [huv]
  ring

lemma GP005B4c_four_coefficients (N S : ℝ) (hN : 4 ≤ N) (hS : 1 ≤ S) (hSN : S ≤ N) (hgap : S = N ∨ S+1 ≤ N) :
    let C := S*(N-S)/(N*(N-1))
    let A := S*(S-1)/(N*(N-1)) -
      2*(S*(S-1)*(S-2)/(N*(N-1)*(N-2))) +
      S*(S-1)*(S-2)*(S-3)/(N*(N-1)*(N-2)*(N-3))
    0 ≤ A ∧ 0 ≤ C ∧ A ≤ C ∧ 3*(N-2)*A ≤ (N-1)*C ∧
      S/N - 7*(S*(S-1)/(N*(N-1))) +
        12*(S*(S-1)*(S-2)/(N*(N-1)*(N-2))) -
        6*(S*(S-1)*(S-2)*(S-3)/(N*(N-1)*(N-2)*(N-3))) = C-6*A := by
  dsimp only
  let C := S*(N-S)/(N*(N-1))
  let R := (S-1)*(N-S-1)/((N-2)*(N-3))
  have n0 : N ≠ 0 := by linarith
  have n1 : N-1 ≠ 0 := by linarith
  have n2 : N-2 ≠ 0 := by linarith
  have n3 : N-3 ≠ 0 := by linarith
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N-1 := by linarith
  have hN2 : 0 < N-2 := by linarith
  have hN3 : 0 < N-3 := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hS1 : 0 ≤ S-1 := by linarith
  have hNS : 0 ≤ N-S := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hEq : S*(S-1)/(N*(N-1)) -
      2*(S*(S-1)*(S-2)/(N*(N-1)*(N-2))) +
      S*(S-1)*(S-2)*(S-3)/(N*(N-1)*(N-2)*(N-3)) = C*R := by
    dsimp [C, R]
    field_simp [n0, n1, n2, n3]
    <;> ring
  have hA : 0 ≤ C*R := by
    by_cases h : S = N
    · subst S
      simp [C]
    · have hgap' : 1 ≤ N-S := by
        rcases hgap with he | he
        · exact (h he).elim
        · linarith
      have hNS1 : 0 ≤ N-S-1 := by linarith
      exact mul_nonneg hC (by dsimp [R]; positivity)
  have hpoly : 3*(S-1)*(N-S-1) ≤ (N-1)*(N-3) := by
    have := mul_nonneg (by linarith : 0 ≤ N) (by linarith : 0 ≤ N-4)
    nlinarith [sq_nonneg (2*S-N)]
  have hRat : 3*(N-2)*R ≤ N-1 := by
    dsimp [R]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < (N-2)*(N-3))).mpr
    have hh := mul_le_mul_of_nonneg_left hpoly (by linarith : 0 ≤ N-2)
    nlinarith
  have h3 : 3*(N-2)*(C*R) ≤ (N-1)*C := by
    nlinarith [mul_le_mul_of_nonneg_left hRat hC]
  have hAC : C*R ≤ C := by nlinarith
  rw [hEq]
  refine ⟨hA, hC, hAC, h3, ?_⟩
  dsimp [C, R]
  field_simp [n0, n1, n2, n3]
  <;> ring

lemma GP005B4c_expectation_const {n s : ℕ} (hsn : s ≤ n) (c : ℝ) :
    expectation s (fun _ : Finset (Fin n) => c) = c := by
  have hcard : ((design n s).card : ℝ) ≠ 0 := by
    simp only [design, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (Nat.choose_pos hsn).ne'
  simp only [expectation, Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hcard

lemma GP005B4c_variance_identity {n s : ℕ} (hsn : s ≤ n)
    (f : Finset (Fin n) → ℝ) :
    variance s f = expectation s (fun S => f S^2) - (expectation s f)^2 := by
  have hf : (fun S => (f S-expectation s f)^2) =
      (fun S => (f S^2-(2*expectation s f)*f S)+(expectation s f)^2) := by
    funext S
    ring
  unfold variance
  rw [hf, control_arm_expectation_add, control_arm_expectation_sub,
    expectation_mul, GP005B4c_expectation_const hsn]
  ring

lemma GP005B4c_variance_le_second {n s : ℕ} (hsn : s ≤ n)
    (f : Finset (Fin n) → ℝ) : variance s f ≤ expectation s (fun S => f S^2) := by
  rw [GP005B4c_variance_identity hsn]
  linarith [sq_nonneg (expectation s f)]

lemma GP005B4c_four_bound {n s : ℕ} (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (u v : Fin n → ℝ) (hu : (∑ i, u i)=0) (hv : (∑ i, v i)=0) :
    expectation s (fun S => (mean S u*mean S v)^2) ≤
      ((n : ℝ)-s)*n/((s : ℝ)^3*(n-1))*
        popMean (fun i => u i^2)*popMean (fun i => v i^2) := by
  let C := (s : ℝ)*((n : ℝ)-s)/((n : ℝ)*(n-1))
  let A := (s : ℝ)*(s-1)/((n : ℝ)*(n-1)) -
    2*((s : ℝ)*(s-1)*(s-2)/((n : ℝ)*(n-1)*(n-2))) +
    (s : ℝ)*(s-1)*(s-2)*(s-3)/((n : ℝ)*(n-1)*(n-2)*(n-3))
  let U := ∑ i, u i^2
  let V := ∑ i, v i^2
  let W := ∑ i, u i*v i
  let D := ∑ i, u i^2*v i^2
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hsnR : (s : ℝ) ≤ n := by exact_mod_cast hsn
  have hgap : (s : ℝ) = n ∨ (s : ℝ)+1 ≤ n := by
    rcases eq_or_lt_of_le hsn with he | he
    · exact Or.inl (by exact_mod_cast he)
    · exact Or.inr (by exact_mod_cast (show s+1 ≤ n by omega))
  obtain ⟨hA, hC, hAC, h3, hB⟩ := GP005B4c_four_coefficients (n : ℝ) (s : ℝ)
    hnR hsR hsnR hgap
  change 0 ≤ A at hA
  change 0 ≤ C at hC
  change A ≤ C at hAC
  change 3*((n : ℝ)-2)*A ≤ ((n : ℝ)-1)*C at h3
  have hW : W^2 ≤ U*V := Finset.sum_mul_sq_le_sq_mul_sq univ u v
  have hWD : W^2 ≤ (n : ℝ)*D := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => u i*v i) (fun _ => (1 : ℝ))
    simpa [W, D, mul_pow, mul_comm] using hh
  have hD : D ≤ U*V := by
    calc
      _ ≤ ∑ i, u i^2*V := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (mem_univ i)) (sq_nonneg _)
      _ = _ := by dsimp [U]; rw [Finset.sum_mul]
  have hUV : 0 ≤ U*V := mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
    (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hbound := GP005B4c_four_comparison (n : ℝ) A C (U*V) (W^2) D
    hnR hA hC hUV hW hD hWD hAC h3
  rw [GP005B4c_four_moment hn hs hsn u v hu hv, hB]
  change (A*(U*V+2*W^2)+(C-6*A)*D)/(s : ℝ)^4 ≤ _
  calc
    _ ≤ C*(U*V)/(s : ℝ)^4 := div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by
      dsimp [C, U, V, popMean, mean]
      simp only [Finset.card_univ, Fintype.card_fin]
      have n0 : (n : ℝ) ≠ 0 := by linarith
      have s0 : (s : ℝ) ≠ 0 := by linarith
      have n1 : (n : ℝ)-1 ≠ 0 := by linarith
      field_simp [n0, s0, n1]
      <;> ring

lemma GP005B4c_centered_sum {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    (∑ i, centered a i)=0 := by
  have hh := control_arm_pop_centered hn a
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simpa [popMean, mean, n0] using hh

lemma GP005B4c_variance_mean {n s : ℕ} (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (a : Fin n → ℝ) :
    variance s (fun S => mean S a) = ((n : ℝ)-s)/((s : ℝ)*(n-1))*
      popMean (fun i => (a i-popMean a)^2) := by
  unfold variance
  rw [mean_unbiased (by omega) hs hsn]
  have hf : ∀ S ∈ design n s, (mean S a-popMean a)^2 =
      mean S (centered a)*mean S (centered a) := by
    intro S hS
    have hc : S.card = s := control_arm_card S hS
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    change (mean S a-popMean a)^2 =
      mean S (fun i => a i-popMean a)*mean S (fun i => a i-popMean a)
    rw [mean_sub, mean_const S hne, pow_two]
  rw [expectation_congr s _ _ hf, control_arm_centered_mean_product (by omega) hs hsn
    _ _ (control_arm_pop_centered (by omega) a)]
  simp only [centered, pow_two]

lemma GP005B4c_covariance_treated {n s : ℕ} (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (a b : Fin n → ℝ) :
    variance s (fun S => sampleCov S a b) ≤ covarianceBound s (centered a) (centered b) := by
  have hloc : ∀ S ∈ design n s, sampleCov S a b = sampleCov S (centered a) (centered b) := by
    intro S hS
    have hc : S.card = s := control_arm_card S hS
    exact (covariance_location_invariant S (Finset.card_pos.mp (by omega))
      a b (popMean a) (popMean b)).symm
  have hvar : variance s (fun S => sampleCov S a b) =
      variance s (fun S => sampleCov S (centered a) (centered b)) := by
    unfold variance
    rw [expectation_congr s _ _ hloc]
    exact expectation_congr s _ _ (fun S hS => by dsimp only; rw [hloc S hS])
  rw [hvar]
  exact le_trans (variance_difference_bound s
    (fun S => mean S (fun i => centered a i*centered b i))
    (fun S => mean S (centered a)*mean S (centered b))) (by
      rw [GP005B4c_variance_mean hn hs hsn]
      have hv := (GP005B4c_variance_le_second hsn
        (fun S => mean S (centered a)*mean S (centered b))).trans
        (GP005B4c_four_bound hn hs hsn (centered a) (centered b)
          (GP005B4c_centered_sum (by omega) a) (GP005B4c_centered_sum (by omega) b))
      unfold covarianceBound
      convert add_le_add_left (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2))
        (2*(((n : ℝ)-s)/((s : ℝ)*(n-1))*
          popMean (fun i => (centered a i*centered b i-
            popMean (fun j => centered a j*centered b j))^2))) using 1 <;> ring)

lemma GP005B4c_covariance_arm {n m : ℕ} (hn : 4 ≤ n) (hm : 0 < m) (hmn : m < n)
    (t : Arm) (a b : Fin n → ℝ) :
    variance m (fun S => sampleCov (armSet t S) a b) ≤
      covarianceBound (armSize n m t) (centered a) (centered b) := by
  cases t with
  | treated => exact GP005B4c_covariance_treated hn hm hmn.le a b
  | control =>
    change variance m (fun S => sampleCov (control S) a b) ≤ _
    have hvar : variance m (fun S => sampleCov (control S) a b) =
        variance (n-m) (fun S => sampleCov S a b) := by
      unfold variance
      dsimp only
      rw [control_arm_transport hmn.le (fun S => sampleCov S a b)]
      exact control_arm_transport hmn.le
        (fun S => (sampleCov S a b-expectation (n-m) (fun A => sampleCov A a b))^2)
    rw [hvar]
    exact GP005B4c_covariance_treated hn (by omega) (by omega) a b

theorem corrected_leverage_variance_chain_proof {n d m : ℕ} (P : Population n d)
    (hn : 4 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (t : Arm) (K : ℝ)
    (hK : popMean (fun i => (if t = .treated then P.yT i else P.yC i)^2) ≤ K) :
    let y := if t = .treated then P.yT else P.yC
    let u := fun i => leverage P i - (d : ℝ)
    let v := centered y
    popMean (leverage P) = d ∧
    (∀ i, 0 ≤ leverage P i ∧ leverage P i ≤ n * kappa P ∧ |u i| ≤ n * kappa P) ∧
    (d : ℝ) ≤ n * kappa P ∧
    popMean (fun i => u i^2) = popMean (fun i => leverage P i^2) - (d : ℝ)^2 ∧
    popMean (fun i => u i^2) ≤ n * kappa P * d ∧
    popMean (fun i => v i^2) = popMean (fun i => y i^2) - popMean y^2 ∧
    popMean (fun i => v i^2) ≤ K ∧
    popMean (fun i => (u i * v i - popMean (fun j => u j*v j))^2) ≤
      popMean (fun i => u i^2 * v i^2) ∧
    popMean (fun i => u i^2 * v i^2) ≤ (n : ℝ)^2 * kappa P^2 * K ∧
    variance m (fun S => sampleCov (armSet t S) (leverage P) y) ≤
      covarianceBound (armSize n m t) u v ∧
    covarianceBound (armSize n m t) u v ≤
      2 * ((n : ℝ)-armSize n m t) / ((armSize n m t : ℝ)*(n-1)) * (n : ℝ)^2 * kappa P^2 * K +
      2 * ((n : ℝ)-armSize n m t) * n / ((armSize n m t : ℝ)^3*(n-1)) * n * kappa P * d * K := by
  classical
  let y := if t = .treated then P.yT else P.yC
  let u := fun i => leverage P i-(d : ℝ)
  let v := centered y
  let s := armSize n m t
  have hnpos : 0 < n := by omega
  have hKy : popMean (fun i => y i^2) ≤ K := by
    cases t <;> simpa only [y, reduceCtorEq, if_true, if_false] using hK
  obtain ⟨hd, hu, huEq, huBound, hvEq, hvBound, hprod, huv⟩ :=
    centered_leverage_moment_bounds P hnpos hP.2 y K hKy
  have hmean : popMean (leverage P) = d := leverage_population_mean P hP.2
  have hCov : variance m (fun S => sampleCov (armSet t S) (leverage P) y) ≤
      covarianceBound s u v := by
    have hh := GP005B4c_covariance_arm hn hm hmn t (leverage P) y
    change variance m (fun S => sampleCov (armSet t S) (leverage P) y) ≤
      covarianceBound s (fun i => leverage P i-popMean (leverage P)) v at hh
    simpa only [hmean] using hh
  have hspos : 0 < s := by cases t <;> simp only [s, armSize] <;> omega
  have hslt : s < n := by cases t <;> simp only [s, armSize] <;> omega
  have hsR : (0 : ℝ) < s := by exact_mod_cast hspos
  have hnsR : (s : ℝ) < n := by exact_mod_cast hslt
  have hn1R : (0 : ℝ) < n-1 := by
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let A : ℝ := 2*((n : ℝ)-s)/((s : ℝ)*(n-1))
  let B : ℝ := 2*((n : ℝ)-s)*n/((s : ℝ)^3*(n-1))
  have hns0 : (0 : ℝ) ≤ n-s := sub_nonneg.mpr hnsR.le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hu0 : 0 ≤ popMean (fun i => u i^2) := by
    unfold popMean mean
    exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Nat.cast_nonneg _)
  have hv0 : 0 ≤ popMean (fun i => v i^2) := by
    unfold popMean mean
    exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Nat.cast_nonneg _)
  have hnkd : 0 ≤ (n : ℝ)*kappa P*d := hu0.trans huBound
  have hprodB : popMean (fun i => u i^2)*popMean (fun i => v i^2) ≤
      ((n : ℝ)*kappa P*d)*K := mul_le_mul huBound hvBound hv0 hnkd
  have hfinal : covarianceBound s u v ≤
      A*(n : ℝ)^2*kappa P^2*K+B*n*kappa P*d*K := by
    calc
      covarianceBound s u v =
          A * popMean (fun i => (u i*v i-popMean (fun j => u j*v j))^2) +
          B * (popMean (fun i => u i^2)*popMean (fun i => v i^2)) := by
        dsimp only [covarianceBound, A, B]
        ring
      _ ≤ A*((n : ℝ)^2*kappa P^2*K)+B*(((n : ℝ)*kappa P*d)*K) :=
        add_le_add (mul_le_mul_of_nonneg_left (hprod.trans huv) hA)
          (mul_le_mul_of_nonneg_left hprodB hB)
      _ = A*(n : ℝ)^2*kappa P^2*K+B*n*kappa P*d*K := by ring
  dsimp only
  refine ⟨hmean, ?_, hd, huEq, huBound, hvEq, hvBound, hprod, huv, hCov, hfinal⟩
  intro i
  exact ⟨leverage_nonneg P i, leverage_le_maximum P hnpos i, hu i⟩

end
end AronowAudit.P005.Wave1
