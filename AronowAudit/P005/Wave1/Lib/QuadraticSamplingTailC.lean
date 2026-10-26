import AronowAudit.P005.Wave1.Gap.GP005B4c
import AronowAudit.P005.Wave1.Cond.CondP002P005P006Proofs

/-!
Finite principal-matrix sampling: the full Lei--Ding quadratic sampling lemma,
including nonsymmetric matrices and the empty and full samples.
-/

noncomputable section
open scoped BigOperators Matrix
open Finset
set_option maxRecDepth 3000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace AronowAudit.P005.Wave1

open AronowAudit.Literature

attribute [local instance] Classical.propDecidable

/-- Express a principal sum using the labelled inclusion indicators. -/
theorem qtc_principal_indicator {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) :
    principalSum n Q S = ∑ i, ∑ j, Q i j * (indicator S i * indicator S j) := by
  symm
  calc
    _ = ∑ i, indicator S i * (∑ j, indicator S j * Q i j) := by
      simp only [Finset.mul_sum]
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      ring
    _ = principalSum n Q S := by
      simp_rw [indicator_sum]
      rfl

/-- The unrestricted first moment, initially for a nonempty sample. -/
theorem qtc_expectation_positive {n s : ℕ} (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    expectation s (principalSum n Q) =
      (s : ℝ)*((n : ℝ)-s)/((n : ℝ)*(n-1)) * (∑ i, Q i i) +
      (s : ℝ)*(s-1)/((n : ℝ)*(n-1)) * (∑ i, ∑ j, Q i j) := by
  have hf : principalSum n Q =
      (fun S => ∑ i, ∑ j, Q i j * (indicator S i * indicator S j)) := by
    funext S
    exact qtc_principal_indicator Q S
  rw [hf, expectation_sum]
  simp_rw [expectation_sum, expectation_mul,
    control_arm_pair_indicator (by omega : 3 ≤ n) hs hsn]
  simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change (∑ i, ∑ j, Q i j * ((s : ℝ)*(s-1)/((n : ℝ)*(n-1)))) +
      (∑ i, Q i i * ((s : ℝ)/n - (s : ℝ)*(s-1)/((n : ℝ)*(n-1)))) = _
  simp only [← Finset.sum_mul]
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have n0 : (n : ℝ) ≠ 0 := by linarith
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  field_simp [n0, n1]
  ring

/-- Contract all fifteen four-indicator equality patterns against a centered
matrix. No rank-one restriction is used. -/
theorem qtc_matrix_delta_sum {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hr : ∀ i, (∑ j, H i j) = 0) (hc : ∀ j, (∑ i, H i j) = 0)
    (p1 p2 p3 p4 : ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, H i j * H k l * (
      p4 + (if i=j then p3-p4 else 0) + (if i=k then p3-p4 else 0) +
      (if i=l then p3-p4 else 0) + (if j=k then p3-p4 else 0) +
      (if j=l then p3-p4 else 0) + (if k=l then p3-p4 else 0) +
      (if i=j ∧ i=k then p2-3*p3+2*p4 else 0) +
      (if i=j ∧ i=l then p2-3*p3+2*p4 else 0) +
      (if i=k ∧ i=l then p2-3*p3+2*p4 else 0) +
      (if j=k ∧ j=l then p2-3*p3+2*p4 else 0) +
      (if i=j ∧ k=l then p2-2*p3+p4 else 0) +
      (if i=k ∧ j=l then p2-2*p3+p4 else 0) +
      (if i=l ∧ j=k then p2-2*p3+p4 else 0) +
      (if i=j ∧ i=k ∧ i=l then p1-7*p2+12*p3-6*p4 else 0))) =
      (p2-2*p3+p4)*((∑ i, H i i)^2 + (∑ i, ∑ j, (H i j)^2) +
        (∑ i, ∑ j, H i j * H j i)) +
      (p1-7*p2+12*p3-6*p4)*(∑ i, (H i i)^2) := by
  have hexpand : ∀ i j k l : Fin n,
      H i j * H k l * (
      p4 + (if i=j then p3-p4 else 0) + (if i=k then p3-p4 else 0) +
      (if i=l then p3-p4 else 0) + (if j=k then p3-p4 else 0) +
      (if j=l then p3-p4 else 0) + (if k=l then p3-p4 else 0) +
      (if i=j ∧ i=k then p2-3*p3+2*p4 else 0) +
      (if i=j ∧ i=l then p2-3*p3+2*p4 else 0) +
      (if i=k ∧ i=l then p2-3*p3+2*p4 else 0) +
      (if j=k ∧ j=l then p2-3*p3+2*p4 else 0) +
      (if i=j ∧ k=l then p2-2*p3+p4 else 0) +
      (if i=k ∧ j=l then p2-2*p3+p4 else 0) +
      (if i=l ∧ j=k then p2-2*p3+p4 else 0) +
      (if i=j ∧ i=k ∧ i=l then p1-7*p2+12*p3-6*p4 else 0)) =
      p4 * H i j * H k l +
      (if i=j then (p3-p4)*H i j*H k l else 0) +
      (if i=k then (p3-p4)*H i j*H k l else 0) +
      (if i=l then (p3-p4)*H i j*H k l else 0) +
      (if j=k then (p3-p4)*H i j*H k l else 0) +
      (if j=l then (p3-p4)*H i j*H k l else 0) +
      (if k=l then (p3-p4)*H i j*H k l else 0) +
      (if i=j ∧ i=k then (p2-3*p3+2*p4)*H i j*H k l else 0) +
      (if i=j ∧ i=l then (p2-3*p3+2*p4)*H i j*H k l else 0) +
      (if i=k ∧ i=l then (p2-3*p3+2*p4)*H i j*H k l else 0) +
      (if j=k ∧ j=l then (p2-3*p3+2*p4)*H i j*H k l else 0) +
      (if i=j ∧ k=l then (p2-2*p3+p4)*H i j*H k l else 0) +
      (if i=k ∧ j=l then (p2-2*p3+p4)*H i j*H k l else 0) +
      (if i=l ∧ j=k then (p2-2*p3+p4)*H i j*H k l else 0) +
      (if i=j ∧ i=k ∧ i=l then (p1-7*p2+12*p3-6*p4)*H i j*H k l else 0) := by
    intro i j k l
    simp only [mul_add, mul_ite, mul_zero, ite_and]
    ring
  simp_rw [hexpand, Finset.sum_add_distrib]
  have h0 : (∑ i, ∑ j, ∑ k, ∑ l, p4*H i j*H k l) = 0 := by
    simp only [← Finset.mul_sum, hr, mul_zero, Finset.sum_const_zero]
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l,
      if i=j then (p3-p4)*H i j*H k l else 0) = 0 := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [← Finset.mul_sum, hr, mul_zero, Finset.sum_const_zero]
  have h2 : (∑ i, ∑ j, ∑ k, ∑ l,
      if i=k then (p3-p4)*H i j*H k l else 0) = 0 := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [← Finset.mul_sum, hr, mul_zero, Finset.sum_const_zero]
  have h3 : (∑ i, ∑ j, ∑ k, ∑ l,
      if i=l then (p3-p4)*H i j*H k l else 0) = 0 := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [← Finset.mul_sum, hc, mul_zero, Finset.sum_const_zero]
  have h4 : (∑ i, ∑ j, ∑ k, ∑ l,
      if j=k then (p3-p4)*H i j*H k l else 0) = 0 := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [← Finset.mul_sum, hr, mul_zero, Finset.sum_const_zero]
  have h5 : (∑ i, ∑ j, ∑ k, ∑ l,
      if j=l then (p3-p4)*H i j*H k l else 0) = 0 := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [← Finset.mul_sum, hc, mul_zero, Finset.sum_const_zero]
  have h6 : (∑ i, ∑ j, ∑ k, ∑ l,
      if k=l then (p3-p4)*H i j*H k l else 0) = 0 := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hr,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h7 : (∑ i, ∑ j, ∑ k, ∑ l,
      if i=j ∧ i=k then (p2-3*p3+2*p4)*H i j*H k l else 0) = 0 := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [← Finset.mul_sum, hr, mul_zero, Finset.sum_const_zero]
  have h8 : (∑ i, ∑ j, ∑ k, ∑ l,
      if i=j ∧ i=l then (p2-3*p3+2*p4)*H i j*H k l else 0) = 0 := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [← Finset.mul_sum, hc, mul_zero, Finset.sum_const_zero]
  have h9 : (∑ i, ∑ j, ∑ k, ∑ l,
      if i=k ∧ i=l then (p2-3*p3+2*p4)*H i j*H k l else 0) = 0 := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [← Finset.sum_mul, ← Finset.mul_sum, hr,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h10 : (∑ i, ∑ j, ∑ k, ∑ l,
      if j=k ∧ j=l then (p2-3*p3+2*p4)*H i j*H k l else 0) = 0 := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← Finset.mul_sum, hc,
      mul_zero, zero_mul, Finset.sum_const_zero]
  have h11 : (∑ i, ∑ j, ∑ k, ∑ l,
      if i=j ∧ k=l then (p2-2*p3+p4)*H i j*H k l else 0) =
      (p2-2*p3+p4)*(∑ i, H i i)^2 := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
    ring
  have h12 : (∑ i, ∑ j, ∑ k, ∑ l,
      if i=k ∧ j=l then (p2-2*p3+p4)*H i j*H k l else 0) =
      (p2-2*p3+p4)*(∑ i, ∑ j, (H i j)^2) := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [Finset.mul_sum, pow_two, mul_assoc]
  have h13 : (∑ i, ∑ j, ∑ k, ∑ l,
      if i=l ∧ j=k then (p2-2*p3+p4)*H i j*H k l else 0) =
      (p2-2*p3+p4)*(∑ i, ∑ j, H i j*H j i) := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [Finset.mul_sum, mul_assoc]
  have h14 : (∑ i, ∑ j, ∑ k, ∑ l,
      if i=j ∧ i=k ∧ i=l then (p1-7*p2+12*p3-6*p4)*H i j*H k l else 0) =
      (p1-7*p2+12*p3-6*p4)*(∑ i, (H i i)^2) := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [Finset.mul_sum, pow_two, mul_assoc]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  ring

/-- The second moment is a four-indicator contraction. -/
theorem qtc_principal_square {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) :
    (principalSum n H S)^2 = ∑ i, ∑ j, ∑ k, ∑ l,
      (H i j * H k l) *
        (indicator S i * indicator S j * indicator S k * indicator S l) := by
  rw [qtc_principal_indicator, pow_two]
  simp only [Finset.sum_mul, Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

/-- Exact centered-matrix second moment, retaining the transpose contraction. -/
theorem qtc_matrix_second_moment {n s : ℕ} (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hr : ∀ i, (∑ j, H i j) = 0) (hc : ∀ j, (∑ i, H i j) = 0) :
    let p1 := (s : ℝ)/n
    let p2 := (s : ℝ)*(s-1)/((n : ℝ)*(n-1))
    let p3 := (s : ℝ)*(s-1)*(s-2)/((n : ℝ)*(n-1)*(n-2))
    let p4 := (s : ℝ)*(s-1)*(s-2)*(s-3)/((n : ℝ)*(n-1)*(n-2)*(n-3))
    expectation s (fun S => (principalSum n H S)^2) =
      (p2-2*p3+p4)*((∑ i, H i i)^2 + (∑ i, ∑ j, (H i j)^2) +
        (∑ i, ∑ j, H i j * H j i)) +
      (p1-7*p2+12*p3-6*p4)*(∑ i, (H i i)^2) := by
  dsimp only
  simp_rw [qtc_principal_square, expectation_sum, expectation_mul,
    GP005B4c_four_indicator hn hs hsn]
  exact qtc_matrix_delta_sum H hr hc _ _ _ _

/-- The coefficient identity responsible for the centered quadratic variance
bound. Here `A` is the probability of two disjoint selected/unselected pairs. -/
theorem qtc_coefficient_identity (N S : ℝ) (hN : 4 ≤ N) :
    let C := S*(N-S)/(N*(N-1))
    let A := S*(S-1)/(N*(N-1)) -
      2*(S*(S-1)*(S-2)/(N*(N-1)*(N-2))) +
      S*(S-1)*(S-2)*(S-3)/(N*(N-1)*(N-2)*(N-3))
    (C-6*A)+N*(A-C^2) = -2*N*A/(N-1) := by
  dsimp only
  have n0 : N ≠ 0 := by linarith
  have n1 : N-1 ≠ 0 := by linarith
  have n2 : N-2 ≠ 0 := by linarith
  have n3 : N-3 ≠ 0 := by linarith
  field_simp [n0, n1, n2, n3]
  ring

/-- An elementary comparison for the exact symmetric variance formula. -/
theorem qtc_variance_comparison (N A C D F Z : ℝ)
    (hA : 0 ≤ A)
    (hD0 : 0 ≤ D) (hF0 : 0 ≤ F) (hZ0 : 0 ≤ Z)
    (hDF : D ≤ F) (hZD : Z ≤ N*D) (h2 : 2*A ≤ C)
    (hcoef : (C-6*A)+N*(A-C^2) ≤ 0) :
    (C-6*A)*D+2*A*F+(A-C^2)*Z ≤ C*F := by
  by_cases hB : 0 ≤ A-C^2
  · have h1 := mul_le_mul_of_nonneg_left hZD hB
    have h2' := mul_nonpos_of_nonpos_of_nonneg hcoef hD0
    have h3 := mul_le_mul_of_nonneg_right h2 hF0
    nlinarith
  · have hB' : A-C^2 ≤ 0 := le_of_not_ge hB
    have h1 := mul_nonpos_of_nonpos_of_nonneg hB' hZ0
    by_cases hE : 0 ≤ C-6*A
    · have h2' := mul_le_mul_of_nonneg_left hDF hE
      have h3 := mul_nonneg hA hF0
      nlinarith
    · have h2' := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hE) hD0
      have h3 := mul_le_mul_of_nonneg_right h2 hF0
      nlinarith

/-- Exact variance identity for a symmetric matrix with vanishing row sums. -/
theorem qtc_symmetric_variance_identity {n s : ℕ}
    (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i j, H i j = H j i) (hr : ∀ i, (∑ j, H i j) = 0) :
    let C := (s : ℝ)*((n : ℝ)-s)/((n : ℝ)*(n-1))
    let A := (s : ℝ)*(s-1)/((n : ℝ)*(n-1)) -
      2*((s : ℝ)*(s-1)*(s-2)/((n : ℝ)*(n-1)*(n-2))) +
      (s : ℝ)*(s-1)*(s-2)*(s-3)/((n : ℝ)*(n-1)*(n-2)*(n-3))
    variance s (principalSum n H) =
      (C-6*A)*(∑ i, (H i i)^2) + 2*A*(∑ i, ∑ j, (H i j)^2) +
        (A-C^2)*(∑ i, H i i)^2 := by
  dsimp only
  have hc : ∀ j, (∑ i, H i j) = 0 := by
    intro j
    simpa only [hsym] using hr j
  have htotal : (∑ i, ∑ j, H i j) = 0 := by simp only [hr, Finset.sum_const_zero]
  have hcross : (∑ i, ∑ j, H i j*H j i) = ∑ i, ∑ j, (H i j)^2 := by
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    rw [← hsym _ _, pow_two]
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsnR : (s : ℝ) ≤ n := by exact_mod_cast hsn
  have hgap : (s : ℝ) = n ∨ (s : ℝ)+1 ≤ n := by
    rcases eq_or_lt_of_le hsn with he | he
    · exact Or.inl (by exact_mod_cast he)
    · exact Or.inr (by exact_mod_cast (show s+1 ≤ n by omega))
  obtain ⟨_, _, _, _, hcoef⟩ := GP005B4c_four_coefficients (n : ℝ) (s : ℝ)
    hnR hsR hsnR hgap
  rw [GP005B4c_variance_identity hsn, qtc_matrix_second_moment hn hs hsn H hr hc,
    qtc_expectation_positive hn hs hsn, htotal, mul_zero, add_zero, hcross, hcoef]
  ring

/-- The symmetric principal-sum bound at every positive sample size, including
the full population. -/
theorem qtc_symmetric_variance_bound {n s : ℕ}
    (hn : 4 ≤ n) (hs : 0 < s) (hsn : s ≤ n)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i j, H i j = H j i) (hr : ∀ i, (∑ j, H i j) = 0) :
    variance s (principalSum n H) ≤
      (s : ℝ)*((n : ℝ)-s)/((n : ℝ)*(n-1)) * (∑ i, ∑ j, (H i j)^2) := by
  let C := (s : ℝ)*((n : ℝ)-s)/((n : ℝ)*(n-1))
  let A := (s : ℝ)*(s-1)/((n : ℝ)*(n-1)) -
    2*((s : ℝ)*(s-1)*(s-2)/((n : ℝ)*(n-1)*(n-2))) +
    (s : ℝ)*(s-1)*(s-2)*(s-3)/((n : ℝ)*(n-1)*(n-2)*(n-3))
  let D := ∑ i, (H i i)^2
  let F := ∑ i, ∑ j, (H i j)^2
  let T := ∑ i, H i i
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsnR : (s : ℝ) ≤ n := by exact_mod_cast hsn
  have hgap : (s : ℝ) = n ∨ (s : ℝ)+1 ≤ n := by
    rcases eq_or_lt_of_le hsn with he | he
    · exact Or.inl (by exact_mod_cast he)
    · exact Or.inr (by exact_mod_cast (show s+1 ≤ n by omega))
  obtain ⟨hA, hC, _, h3, _⟩ := GP005B4c_four_coefficients (n : ℝ) (s : ℝ)
    hnR hsR hsnR hgap
  change 0 ≤ A at hA
  change 0 ≤ C at hC
  change 3*((n : ℝ)-2)*A ≤ ((n : ℝ)-1)*C at h3
  have h2 : 2*A ≤ C := by
    have hh := mul_nonneg (by linarith : 0 ≤ (n : ℝ)-4) hA
    nlinarith
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hDF : D ≤ F := Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (fun j _ => sq_nonneg (H i j)) (mem_univ i)
  have hTD : T^2 ≤ (n : ℝ)*D := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => H i i) (fun _ => (1 : ℝ))
    simpa [T, D, mul_comm] using hh
  have hid := qtc_coefficient_identity (n : ℝ) (s : ℝ) hnR
  change (C-6*A)+(n : ℝ)*(A-C^2) = -2*(n : ℝ)*A/((n : ℝ)-1) at hid
  have hcoef : (C-6*A)+(n : ℝ)*(A-C^2) ≤ 0 := by
    rw [hid]
    exact div_nonpos_of_nonpos_of_nonneg
      (by nlinarith [mul_nonneg (by linarith : 0 ≤ (n : ℝ)) hA]) (by linarith)
  rw [qtc_symmetric_variance_identity hn hs hsn H hsym hr]
  exact qtc_variance_comparison (n : ℝ) A C D F (T^2) hA
    hD0 hF0 (sq_nonneg T) hDF hTD h2 hcoef

/-- The symmetric part has the same principal sums as the original matrix. -/
def qtc_symmetrize {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (Q i j + Q j i)/2

theorem qtc_symmetrize_symmetric {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    ∀ i j, qtc_symmetrize Q i j = qtc_symmetrize Q j i := by
  intro i j
  change (Q i j + Q j i)/2 = (Q j i + Q i j)/2
  ring

theorem qtc_symmetrize_rows {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hr : ∀ i, (∑ j, Q i j) = 0) (hc : ∀ j, (∑ i, Q i j) = 0) :
    ∀ i, (∑ j, qtc_symmetrize Q i j) = 0 := by
  change Fin n → Fin n → ℝ at Q
  intro i
  change (∑ j, (Q i j + Q j i)/2) = 0
  simp only [← Finset.sum_div, Finset.sum_add_distrib, hr, hc, add_zero, zero_div]

theorem qtc_symmetrize_principal {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) : principalSum n (qtc_symmetrize Q) S = principalSum n Q S := by
  change Fin n → Fin n → ℝ at Q
  have ht : (∑ i ∈ S, ∑ j ∈ S, Q j i) = ∑ i ∈ S, ∑ j ∈ S, Q i j :=
    Finset.sum_comm
  change (∑ i ∈ S, ∑ j ∈ S, (Q i j + Q j i)/2) = ∑ i ∈ S, ∑ j ∈ S, Q i j
  simp only [← Finset.sum_div, Finset.sum_add_distrib]
  rw [ht]
  ring

/-- Symmetrization is a contraction for the squared Frobenius norm. -/
theorem qtc_symmetrize_sq_sum_le {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, (qtc_symmetrize Q i j)^2) ≤ ∑ i, ∑ j, (Q i j)^2 := by
  change Fin n → Fin n → ℝ at Q
  have ht : (∑ i, ∑ j, (Q j i)^2) = ∑ i, ∑ j, (Q i j)^2 := Finset.sum_comm
  calc
    _ ≤ ∑ i, ∑ j, ((Q i j)^2+(Q j i)^2)/2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      change ((Q i j + Q j i)/2)^2 ≤ ((Q i j)^2+(Q j i)^2)/2
      nlinarith [sq_nonneg (Q i j - Q j i)]
    _ = _ := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [ht]
      ring

/-- P005 first moment for arbitrary real matrices and all sample sizes
between zero and the population size. -/
theorem qtc_principal_expectation {n s : ℕ} (hn : 4 ≤ n) (hsn : s ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    expectation s (principalSum n Q) =
      (s : ℝ)*((n : ℝ)-s)/((n : ℝ)*(n-1)) * (∑ i, Q i i) +
      (s : ℝ)*(s-1)/((n : ℝ)*(n-1)) * (∑ i, ∑ j, Q i j) := by
  by_cases hs : s = 0
  · subst s
    simp [expectation, design, principalSum]
  · exact qtc_expectation_positive hn (Nat.pos_of_ne_zero hs) hsn Q

/-- P005 variance bound for an arbitrary matrix with both vanishing row
and column sums. The empty and full samples are included. -/
theorem qtc_principal_variance {n s : ℕ} (hn : 4 ≤ n) (hsn : s ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℝ)
    (hr : ∀ i, (∑ j, Q i j) = 0) (hc : ∀ j, (∑ i, Q i j) = 0) :
    variance s (principalSum n Q) ≤
      (s : ℝ)*((n : ℝ)-s)/((n : ℝ)*(n-1)) * (∑ i, ∑ j, (Q i j)^2) := by
  by_cases hs : s = 0
  · subst s
    simp [variance, expectation, design, principalSum]
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    have hsame : principalSum n (qtc_symmetrize Q) = principalSum n Q := by
      funext S
      exact qtc_symmetrize_principal Q S
    have hC : 0 ≤ (s : ℝ)*((n : ℝ)-s)/((n : ℝ)*(n-1)) := by
      have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
      have hsnR : (s : ℝ) ≤ n := by exact_mod_cast hsn
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg s) (sub_nonneg.mpr hsnR))
        (mul_nonneg (by linarith) (by linarith))
    calc
      _ = variance s (principalSum n (qtc_symmetrize Q)) := by rw [hsame]
      _ ≤ _ := qtc_symmetric_variance_bound hn hspos hsn (qtc_symmetrize Q)
        (qtc_symmetrize_symmetric Q) (qtc_symmetrize_rows Q hr hc)
      _ ≤ _ := mul_le_mul_of_nonneg_left (qtc_symmetrize_sq_sum_le Q) hC

end AronowAudit.P005.Wave1

namespace AronowAudit.Literature

/-- The published quadratic sampling proposition for arbitrary matrices,
including empty and full samples. -/
theorem leiDing2021QuadraticSampling_proof : LeiDing2021QuadraticSampling := by
  intro N s hN hs Q
  exact ⟨AronowAudit.P005.Wave1.qtc_principal_expectation hN hs Q,
    AronowAudit.P005.Wave1.qtc_principal_variance hN hs Q⟩

end AronowAudit.Literature

namespace AronowAudit.P005.Wave1


/-- Variance corollary in P005 vocabulary, for every sample size `s ≤ n`
and every matrix with vanishing row and column sums. -/
theorem principal_sum_variance_tailC {n s : ℕ} (hn : 4 ≤ n) (hsn : s ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℝ)
    (hr : ∀ i, (∑ j, Q i j) = 0) (hc : ∀ j, (∑ i, Q i j) = 0) :
    variance s (fun S => ∑ i ∈ S, ∑ j ∈ S, Q i j) ≤
      (s : ℝ)*((n : ℝ)-s)/((n : ℝ)*(n-1)) * (∑ i, ∑ j, (Q i j)^2) := by
  exact qtc_principal_variance hn hsn Q hr hc

end AronowAudit.P005.Wave1
