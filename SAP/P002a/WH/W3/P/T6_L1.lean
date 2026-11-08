import SAP.P002a.WH.W3.Leaves
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W3.P.T6_L1

open scoped BigOperators

lemma power_sums (n : ℕ) :
    (∑ j ∈ Finset.range n, (j : ℝ)) = (n : ℝ) * ((n : ℝ)-1) / 2 ∧
    (∑ j ∈ Finset.range n, (j : ℝ)^2) =
      (n : ℝ) * ((n : ℝ)-1) * (2*(n : ℝ)-1) / 6 ∧
    (∑ j ∈ Finset.range n, (j : ℝ)^3) =
      (n : ℝ)^2 * ((n : ℝ)-1)^2 / 4 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    rw [ih.1, ih.2.1, ih.2.2]
    constructor
    · ring
    constructor <;> ring

lemma grid_sums (n : ℕ) (hn : 2 ≤ n) :
    (∑ i, t6Grid n i) = 0 ∧
    (∑ i, t6Grid n i ^ 2) = (n : ℝ) * t6V n ∧
    (∑ i, t6Grid n i ^ 3) = 0 := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (n : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨h1, h2, h3⟩ := power_sums n
  simp only [t6Grid, div_pow]
  rw [Fin.sum_univ_eq_sum_range
      (fun j => (2 * (j : ℝ) - (n : ℝ) + 1) / ((n : ℝ) - 1)),
    Fin.sum_univ_eq_sum_range
      (fun j => (2 * (j : ℝ) - (n : ℝ) + 1)^2 / ((n : ℝ) - 1)^2),
    Fin.sum_univ_eq_sum_range
      (fun j => (2 * (j : ℝ) - (n : ℝ) + 1)^3 / ((n : ℝ) - 1)^3)]
  simp only [← Finset.sum_div]
  constructor
  · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, h1]
    field_simp
    <;> ring
  constructor
  · have he : (∑ i ∈ Finset.range n,
        (2 * (i : ℝ) - (n : ℝ) + 1)^2) =
        4 * (∑ i ∈ Finset.range n, (i : ℝ)^2) +
        (4 - 4 * (n : ℝ)) * (∑ i ∈ Finset.range n, (i : ℝ)) +
        (n : ℝ) * ((n : ℝ)^2 - 2 * (n : ℝ) + 1) := by
      calc
        _ = ∑ i ∈ Finset.range n,
            (4 * (i : ℝ)^2 + (4 - 4 * (n : ℝ)) * (i : ℝ) +
              ((n : ℝ)^2 - 2 * (n : ℝ) + 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          <;> ring
    rw [he, h1, h2]
    dsimp [t6V]
    field_simp [hd]
    <;> ring
  · have he : (∑ i ∈ Finset.range n,
        (2 * (i : ℝ) - (n : ℝ) + 1)^3) =
        8 * (∑ i ∈ Finset.range n, (i : ℝ)^3) +
        (12 - 12 * (n : ℝ)) * (∑ i ∈ Finset.range n, (i : ℝ)^2) +
        (6 * (n : ℝ)^2 - 12 * (n : ℝ) + 6) *
          (∑ i ∈ Finset.range n, (i : ℝ)) +
        (n : ℝ) * (1 - 3 * (n : ℝ) + 3 * (n : ℝ)^2 - (n : ℝ)^3) := by
      calc
        _ = ∑ i ∈ Finset.range n,
            (8 * (i : ℝ)^3 + (12 - 12 * (n : ℝ)) * (i : ℝ)^2 +
              (6 * (n : ℝ)^2 - 12 * (n : ℝ) + 6) * (i : ℝ) +
              (1 - 3 * (n : ℝ) + 3 * (n : ℝ)^2 - (n : ℝ)^3)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          <;> ring
    rw [he, h1, h2, h3]
    have hz :
        8 * ((n : ℝ)^2 * ((n : ℝ) - 1)^2 / 4) +
        (12 - 12 * (n : ℝ)) *
          ((n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6) +
        (6 * (n : ℝ)^2 - 12 * (n : ℝ) + 6) *
          ((n : ℝ) * ((n : ℝ) - 1) / 2) +
        (n : ℝ) * (1 - 3 * (n : ℝ) + 3 * (n : ℝ)^2 - (n : ℝ)^3) = 0 := by
      ring
    rw [hz, zero_div]

lemma grid_bound (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    |t6Grid n i| ≤ 1 := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hi0 : (0 : ℝ) ≤ i.val := by positivity
  have hi1 : (i.val : ℝ) ≤ (n : ℝ) - 1 := by
    have h : (i.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast i.isLt
    linarith
  rw [abs_le]
  dsimp [t6Grid]
  constructor
  · apply (le_div_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) - 1)).mpr
    linarith
  · apply (div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) - 1)).mpr
    linarith

lemma grid_moments (n : ℕ) (hn : 2 ≤ n) :
    mean (t6Grid n) = 0 ∧
    mean (fun i => t6Grid n i ^ 2) = t6V n ∧
    mean (fun i => t6Grid n i ^ 3) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨h1, h2, h3⟩ := grid_sums n hn
  refine ⟨?_, ?_, ?_⟩
  · simp [mean, h1]
  · simp [mean, h2, hn0]
  · simp [mean, h3]

lemma v_bounds (n : ℕ) (hn : 2 ≤ n) :
    1 / 3 ≤ t6V n ∧ t6V n ≤ 1 := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdp : (0 : ℝ) < 3 * ((n : ℝ) - 1) := by linarith
  dsimp [t6V]
  constructor
  · apply (le_div_iff₀ hdp).mpr
    linarith
  · apply (div_le_iff₀ hdp).mpr
    linarith

end SAP.P002a.WH.W3.P.T6_L1

theorem SAP.P002a.WH.W3.T6_L1_proof : SAP.P002a.WH.W3.T6_L1 := by
  intro m hm
  have hn : 2 ≤ m := by omega
  rcases SAP.P002a.WH.W3.P.T6_L1.grid_moments m hn with ⟨h1, h2, h3⟩
  rcases SAP.P002a.WH.W3.P.T6_L1.v_bounds m hn with ⟨hv0, hv1⟩
  exact ⟨h1, h2, h3, SAP.P002a.WH.W3.P.T6_L1.grid_bound m hn, hv0, hv1⟩
