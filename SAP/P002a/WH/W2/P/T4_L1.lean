import SAP.P002a.WH.W2.Leaves
import AronowAudit.P002.Wave1.PrintedTheorem2.N9

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P002a
open scoped BigOperators

namespace SAP.P002a.WH.W2.P.T4_L1

end SAP.P002a.WH.W2.P.T4_L1

theorem SAP.P002a.WH.W2.T4_L1_proof : SAP.P002a.WH.W2.T4_L1 := by
  intro n hn
  have hN2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hN : (n : ℝ) ≠ 0 := ne_of_gt hNpos

  have hsumRange1 (m : ℕ) :
      (∑ i ∈ Finset.range m, (i : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hsumRange2 (m : ℕ) :
      (∑ i ∈ Finset.range m, (i : ℝ) ^ 2) =
        (m : ℝ) * ((m : ℝ) - 1) * (2 * (m : ℝ) - 1) / 6 := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hsum1 :
      (∑ i : Fin n, (i.val : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact hsumRange1 n
  have hsum2 :
      (∑ i : Fin n, (i.val : ℝ) ^ 2) =
        (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℝ) ^ 2) n).trans
      (hsumRange2 n)

  have hx (i : Fin n) :
      gridX i 0 = (2 * (i.val : ℝ) + 1 - (n : ℝ)) / (n : ℝ) := by
    unfold gridX
    ring
  have hcenter : (∑ i : Fin n, gridX i 0) = 0 := by
    simp_rw [hx]
    rw [← Finset.sum_div]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum1]
    ring
  have hxsq (i : Fin n) :
      gridX i 0 ^ 2 =
        (4 * (i.val : ℝ) ^ 2 + 4 * (1 - (n : ℝ)) * (i.val : ℝ) +
          (1 - (n : ℝ)) ^ 2) / (n : ℝ) ^ 2 := by
    rw [hx, div_pow]
    congr 1
    ring
  have hsecond : mean (fun i : Fin n => gridX i 0 ^ 2) =
      ((n : ℝ) ^ 2 - 1) / (3 * (n : ℝ) ^ 2) := by
    unfold mean
    simp_rw [hxsq]
    rw [← Finset.sum_div]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum1, hsum2]
    field_simp [hN] <;> ring
  have hQ : (1 / 4 : ℝ) ≤ mean (fun i : Fin n => gridX i 0 ^ 2) := by
    rw [hsecond]
    apply (le_div_iff₀ (show (0 : ℝ) < 3 * (n : ℝ) ^ 2 by positivity)).2
    have hNsq : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith only [hN2, sq_nonneg ((n : ℝ) - 2)]
    nlinarith only [hNsq]

  have hfourthPoint (i : Fin n) : gridX i 0 ^ 4 < 1 := by
    have hi0 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
    have hiN : (i.val : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt i.isLt
    have hxLo : (-1 : ℝ) < gridX i 0 := by
      rw [hx]
      apply (lt_div_iff₀ hNpos).2
      linarith
    have hxHi : gridX i 0 < (1 : ℝ) := by
      rw [hx]
      apply (div_lt_iff₀ hNpos).2
      linarith
    have hleft : 0 < 1 - gridX i 0 := by linarith
    have hright : 0 < 1 + gridX i 0 := by linarith
    have hsq : 0 < 1 - gridX i 0 ^ 2 := by
      nlinarith only [mul_pos hleft hright]
    have hsum : 0 < 1 + gridX i 0 ^ 2 := by positivity
    nlinarith only [mul_pos hsq hsum]
  have hfourthSum : (∑ i : Fin n, gridX i 0 ^ 4) < (n : ℝ) := by
    calc
      (∑ i : Fin n, gridX i 0 ^ 4) < (∑ i : Fin n, (1 : ℝ)) := by
        apply Finset.sum_lt_sum
        · intro i hi
          exact (hfourthPoint i).le
        · exact ⟨⟨0, by omega⟩, Finset.mem_univ _, hfourthPoint _⟩
      _ = (n : ℝ) := by simp
  have hfourth : mean (fun i : Fin n => gridX i 0 ^ 4) < 1 := by
    unfold mean
    apply (div_lt_iff₀ hNpos).2
    simpa using hfourthSum

  exact ⟨hcenter, hsecond, hQ, hfourth⟩
