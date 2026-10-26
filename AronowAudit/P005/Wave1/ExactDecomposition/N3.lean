import AronowAudit.P005.Wave1.ExactDecompositionBlueprint

set_option autoImplicit false

namespace AronowAudit.P005.Wave1.ExactDecomposition

open AronowAudit.P005 Finset
open scoped BigOperators

noncomputable section

/-- Expand a product of means and collect its diagonal indicator contribution. -/
theorem n3_proof : N3 := by
  classical
  intro hpair n m hn hm hmn a b
  have hnpos : 0 < n := by omega
  have m0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  let p : ℝ := (m : ℝ) / n
  let q : ℝ := (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1))
  have hdiag (i : Fin n) :
      expectation m (fun S => indicator S i * indicator S i) =
        expectation m (fun S => indicator S i) := by
    apply expectation_congr
    intro S _
    by_cases hi : i ∈ S <;> simp [indicator, hi]
  have hmoment (i j : Fin n) :
      expectation m (fun S => indicator S i * indicator S j) =
        q + if i = j then p - q else 0 := by
    by_cases hij : i = j
    · subst j
      rw [hdiag, indicator_expectation hnpos hm hmn]
      simp only [ite_true]
      dsimp only [p]
      ring
    · simpa only [if_neg hij, add_zero] using hpair n m hn hm hmn i j hij
  have hform : ∀ S ∈ design n m,
      mean S a * mean S b = (1 / (m : ℝ)^2) *
        ∑ i, ∑ j, (a i * b j) * (indicator S i * indicator S j) := by
    intro S hS
    have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
    calc
      mean S a * mean S b = (1 / (m : ℝ)^2) *
          ((∑ i, indicator S i * a i) * (∑ j, indicator S j * b j)) := by
        rw [mean, mean, hs, ← indicator_sum S a, ← indicator_sum S b]
        field_simp [m0] <;> ring
      _ = _ := by
        rw [Finset.sum_mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hsum :
      (∑ i, ∑ j, (a i * b j) * (q + if i = j then p - q else 0)) =
        q * ((∑ i, a i) * (∑ j, b j)) + (p - q) * ∑ i, a i * b i := by
    calc
      _ = ∑ i, ∑ j, (q * (a i * b j) +
          if i = j then (p - q) * (a i * b j) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ = (∑ i, ∑ j, q * (a i * b j)) + ∑ i, (p - q) * (a i * b i) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      _ = q * (∑ i, ∑ j, a i * b j) + (p - q) * ∑ i, a i * b i := by
        simp only [Finset.mul_sum]
      _ = _ := by rw [← Finset.sum_mul_sum]
  rw [expectation_congr m _ _ hform, expectation_mul, expectation_sum]
  simp_rw [expectation_sum, expectation_mul, hmoment]
  rw [hsum]
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hnpos
  have n10 : (n : ℝ) - 1 ≠ 0 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  dsimp only [p, q, popCov, sampleCov, popMean, mean]
  simp only [Finset.card_univ, Fintype.card_fin]
  field_simp [m0, n0, n10] <;> ring

end

end AronowAudit.P005.Wave1.ExactDecomposition
