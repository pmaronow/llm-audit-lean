import AronowAudit.P009.P009_Audit

/-!
# Independent labels and the collision comparison

The law below is the independent uniform label distribution on `Fin k → Fin n`.
A finite union bound over position pairs gives its repeated-label probability.
A [0,1]-valued test constant on injective samples changes by at most that probability.

The mathematical collision coupling is standard, e.g. Jayram–Vondrák (2014),
Proposition 1.
-/

namespace AronowAudit.P009.CompleteSampling
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Independent uniform labels, including the empty sample. -/
def labelLaw (n k : ℕ) (hn : 0 < n) : Law (Fin k → Fin n) where
  mass := fun _ => (n : ℝ)⁻¹ ^ k
  nonneg := fun _ => pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) k
  total := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
    rw [← mul_pow, mul_inv_cancel₀ hn0, one_pow]

/-- A fixed pair of distinct positions has collision probability exactly 1/n. -/
theorem pair_collision_probability (n k : ℕ) (hn : 0 < n)
    (i j : Fin k) (hij : i ≠ j) :
    prob (labelLaw n k hn) (fun a => a i = a j) = (n : ℝ)⁻¹ := by
  let E := Equiv.funSplitAt i (Fin n)
  let Ω := {j : Fin k // j ≠ i} → Fin n
  have hs : (∑ a : Fin k → Fin n, if a i = a j then (1 : ℝ) else 0) =
      (Fintype.card Ω : ℝ) := by
    calc
      _ = ∑ b : Fin n × Ω, if b.1 = b.2 ⟨j, hij.symm⟩ then (1 : ℝ) else 0 := by
        apply Fintype.sum_equiv E
        intro a
        rfl
      _ = _ := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        simp
  have hc : Fintype.card (Fin k → Fin n) = n * Fintype.card Ω := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_congr E
  have ht : (n : ℝ) * ((n : ℝ)⁻¹ ^ k * (Fintype.card Ω : ℝ)) = 1 := by
    have h := (labelLaw n k hn).total
    simp only [labelLaw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    rw [hc, Nat.cast_mul] at h
    nlinarith [h]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    _ = (n : ℝ)⁻¹ ^ k * (∑ a : Fin k → Fin n, if a i = a j then (1 : ℝ) else 0) := by
      simp only [prob, mean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : a i = a j <;> simp [h, labelLaw]
    _ = _ := by
      rw [hs]
      apply mul_left_cancel₀ hn0
      rw [mul_inv_cancel₀ hn0]
      exact ht

/-- A repeated-label sample must contain a colliding ordered pair i<j. -/
theorem noninjective_probability_le (n k : ℕ) (hn : 0 < n) :
    prob (labelLaw n k hn) (fun a => ¬Function.Injective a) ≤
      (k : ℝ) * ((k : ℝ) - 1) / (2 * n) := by
  let S : Finset (Fin k × Fin k) := Finset.univ.filter (fun ij => ij.1 < ij.2)
  have hpoint (a : Fin k → Fin n) :
      (if ¬Function.Injective a then (1 : ℝ) else 0) ≤
        ∑ ij ∈ S, if a ij.1 = a ij.2 then 1 else 0 := by
    by_cases ha : Function.Injective a
    · simp only [ha, not_true_eq_false, ite_false]
      apply Finset.sum_nonneg
      intro ij _
      split_ifs <;> norm_num
    · simp only [ha, not_false_eq_true, ite_true]
      have hex : ∃ i j : Fin k, i < j ∧ a i = a j := by
        by_contra h
        apply ha
        intro i j hij
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact h ⟨i, j, hlt, hij⟩
        · exact h ⟨j, i, hgt, hij.symm⟩
      obtain ⟨i, j, hlt, heq⟩ := hex
      have hmem : (i,j) ∈ S := by simp [S, hlt]
      simpa [heq] using (Finset.single_le_sum (f := fun ij => if a ij.1 = a ij.2 then (1:ℝ) else 0)
        (fun ij _ => by split_ifs <;> norm_num) hmem)
  have hb : prob (labelLaw n k hn) (fun a => ¬Function.Injective a) ≤
      ∑ ij ∈ S, prob (labelLaw n k hn) (fun a => a ij.1 = a ij.2) := by
    simp only [prob, mean]
    calc
      _ ≤ ∑ a : Fin k → Fin n, (labelLaw n k hn).mass a *
          (∑ ij ∈ S, if a ij.1 = a ij.2 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro a _
        have h := mul_le_mul_of_nonneg_left (hpoint a) ((labelLaw n k hn).nonneg a)
        by_cases ha : Function.Injective a <;> simpa [ha] using h
      _ = _ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro ij _
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : a ij.1 = a ij.2 <;> simp [h]
  have hS : S.card = k.choose 2 := by
    simpa [S] using (Fintype.card_product_filter_lt (α := Fin k))
  calc
    _ ≤ ∑ ij ∈ S, prob (labelLaw n k hn) (fun a => a ij.1 = a ij.2) := hb
    _ = ∑ _ij ∈ S, (n : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro ij hij
      apply pair_collision_probability
      exact ne_of_lt (Finset.mem_filter.mp hij).2
    _ = (k : ℝ) * ((k : ℝ) - 1) / (2 * n) := by
      simp only [Finset.sum_const, nsmul_eq_mul, hS]
      rw [Nat.cast_choose_two]
      ring

/-- A [0,1]-valued test constant on injective samples differs from that constant
by at most the probability of a repeated label. -/
theorem bounded_test_comparison (n k : ℕ) (hn : 0 < n)
    (F : (Fin k → Fin n) → ℝ) (c : ℝ)
    (hF : ∀ a, 0 ≤ F a ∧ F a ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
    (hinj : ∀ a, Function.Injective a → F a = c) :
    |mean (labelLaw n k hn) F - c| ≤
      prob (labelLaw n k hn) (fun a => ¬Function.Injective a) := by
  rw [← mean_const (labelLaw n k hn) c, ← mean_sub]
  unfold mean prob
  calc
    _ ≤ ∑ a : Fin k → Fin n, |(labelLaw n k hn).mass a * (F a - c)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_of_nonneg ((labelLaw n k hn).nonneg a)]
      apply mul_le_mul_of_nonneg_left _ ((labelLaw n k hn).nonneg a)
      by_cases hi : Function.Injective a
      · simp [hi, hinj a hi]
      · simp only [hi, not_false_eq_true, ite_true]
        rw [abs_le]
        constructor <;> linarith [(hF a).1, (hF a).2, hc.1, hc.2]

end
end AronowAudit.P009.CompleteSampling
