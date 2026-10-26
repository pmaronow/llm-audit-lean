import AronowAudit.P005.Wave1.ExactDecompositionBlueprint

set_option autoImplicit false

namespace AronowAudit.P005.Wave1.ExactDecomposition

open AronowAudit.P005 Finset
open scoped BigOperators

noncomputable section

/-- The off-diagonal inclusion moment, with the singleton design handled separately. -/
theorem n2_proof : N2 := by
  classical
  intro n m hn hm hmn i j hij
  by_cases hm1 : m = 1
  · subst m
    have hz : expectation 1 (fun S => indicator S i * indicator S j) =
        expectation 1 (fun _ : Finset (Fin n) => 0) := by
      apply expectation_congr
      intro S hS
      have hs : S.card = 1 := (Finset.mem_powersetCard.mp hS).2
      by_cases hi : i ∈ S
      · have hj : j ∉ S := by
          intro hj
          exact hij (Finset.card_le_one.mp hs.le i hi j hj)
        simp [indicator, hi, hj]
      · simp [indicator, hi]
    rw [hz]
    simp [expectation]
  · have hm2 : 2 ≤ m := by omega
    have hinc := inclusion_count (m := m) ({i, j} : Finset (Fin n))
      (by rw [Finset.card_pair hij]; exact hm2)
    have hprod : ∀ S : Finset (Fin n),
        indicator S i * indicator S j = if ({i, j} : Finset (Fin n)) ⊆ S then 1 else 0 := by
      intro S
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
        simp [indicator, Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
    have hmoment : expectation m (fun S => indicator S i * indicator S j) =
        ((n - 2).choose (m - 2) : ℝ) / (n.choose m : ℝ) := by
      simp_rw [hprod]
      simpa only [Finset.card_pair hij] using hinc
    have hc1 : n * (n - 1).choose (m - 1) = n.choose m * m := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n),
        Nat.sub_add_cancel (by omega : 1 ≤ m)] using
          Nat.add_one_mul_choose_eq (n - 1) (m - 1)
    have hc2 : (n - 1) * (n - 2).choose (m - 2) =
        (n - 1).choose (m - 1) * (m - 1) := by
      have hn' : n - 2 + 1 = n - 1 := by omega
      have hm' : m - 2 + 1 = m - 1 := by omega
      simpa only [hn', hm'] using Nat.add_one_mul_choose_eq (n - 2) (m - 2)
    have hc1' : (n : ℝ) * ((n - 1).choose (m - 1) : ℝ) =
        (n.choose m : ℝ) * m := by exact_mod_cast hc1
    have hc2' : ((n : ℝ) - 1) * ((n - 2).choose (m - 2) : ℝ) =
        ((n - 1).choose (m - 1) : ℝ) * ((m : ℝ) - 1) := by
      simpa only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n),
        Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] using
          congrArg (fun k : ℕ => (k : ℝ)) hc2
    have hc : (n : ℝ) * ((n : ℝ) - 1) * ((n - 2).choose (m - 2) : ℝ) =
        (n.choose m : ℝ) * m * ((m : ℝ) - 1) := by
      calc
        _ = (n : ℝ) * (((n : ℝ) - 1) * ((n - 2).choose (m - 2) : ℝ)) := by ring
        _ = (n : ℝ) * (((n - 1).choose (m - 1) : ℝ) * ((m : ℝ) - 1)) := by rw [hc2']
        _ = ((n : ℝ) * ((n - 1).choose (m - 1) : ℝ)) * ((m : ℝ) - 1) := by ring
        _ = _ := by rw [hc1']
    have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have n10 : (n : ℝ) - 1 ≠ 0 := by
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have C0 : (n.choose m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hmn)
    rw [hmoment]
    field_simp [n0, n10, C0]
    nlinarith [hc]

end

end AronowAudit.P005.Wave1.ExactDecomposition
