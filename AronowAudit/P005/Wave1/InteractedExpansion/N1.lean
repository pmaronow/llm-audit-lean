import AronowAudit.P005.Wave1.InteractedExpansionBlueprint

set_option autoImplicit false

namespace AronowAudit.P005.Wave1.InteractedExpansion
open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology
noncomputable section

private theorem range_first (m : ℕ) :
    (∑ j ∈ range m, (j : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

private theorem range_second (m : ℕ) :
    (∑ j ∈ range m, (j : ℝ)^2) =
      (m : ℝ) * ((m : ℝ) - 1) * (2 * (m : ℝ) - 1) / 6 := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

/-- The raw-coordinate bound is useful in the later nodes as well. -/
theorem spikeV_abs (n : ℕ) (hn : 3 ≤ n) (i : Fin n) : |spikeV n i| ≤ 1 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  by_cases hi : i.val = 0
  · simp [spikeV, hi]
  · have hiN : i.val - 1 ≤ n - 2 := by omega
    have hn2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 :=
      Nat.cast_sub (by omega)
    have hiR : ((i.val - 1 : ℕ) : ℝ) ≤ (n : ℝ) - 2 := by
      rw [← hn2]; exact_mod_cast hiN
    rw [spikeV, if_neg hi, abs_le]
    constructor
    · have : 0 ≤ 2 * ((i.val - 1 : ℕ) : ℝ) / ((n : ℝ) - 2) := by positivity
      linarith
    · have : 2 * ((i.val - 1 : ℕ) : ℝ) / ((n : ℝ) - 2) ≤ 2 :=
        (div_le_iff₀ hd).2 (by linarith)
      linarith

/-- Full grid moments, including the centering variance. -/
theorem n1_proof : N1 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  have hd : ((m : ℝ) + 1 - 2) ≠ 0 := by linarith
  have hn0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) + 1 ≠ 0 := by linarith
  have hsplit (f : ℝ → ℝ) :
      (∑ i : Fin (m + 1), f (spikeV (m + 1) i)) =
      f 0 + ∑ j ∈ range m, f (-1 + 2 * (j : ℝ) / (((m + 1 : ℕ) : ℝ) - 2)) := by
    rw [Fin.sum_univ_succ]
    simp only [spikeV, Fin.val_zero, Fin.val_succ,
      Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [Fin.sum_univ_eq_sum_range
      (fun j => f (-1 + 2 * (j : ℝ) / (((m + 1 : ℕ) : ℝ) - 2))) m]
  have hv : (∑ i : Fin (m + 1), spikeV (m + 1) i) = 0 := by
    rw [hsplit (fun x => x)]
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, range_first]
    push_cast
    field_simp [hd]
    <;> ring
  have hv2 : (∑ i : Fin (m + 1), spikeV (m + 1) i ^ 2) =
      ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1) /
        (3 * (((m + 1 : ℕ) : ℝ) - 2)) := by
    rw [hsplit (fun x => x^2)]
    have hp (j : ℕ) (c : ℝ) :
        (-1 + 2 * (j : ℝ) / c)^2 =
        1 - 4 * (j : ℝ) / c + 4 * (j : ℝ)^2 / c^2 := by ring
    simp_rw [hp]
    simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum,
      range_first, range_second]
    push_cast
    field_simp [hd]
    <;> ring
  have ha : (∑ i : Fin (m + 1), spikeA (m + 1) i) = 1 := by
    have hv' : (∑ i : Fin m, spikeV (m + 1) i.succ) = 0 := by
      simpa [Fin.sum_univ_succ, spikeV] using hv
    rw [Fin.sum_univ_succ]
    simp only [spikeA, Fin.val_zero, Fin.val_succ,
      Nat.succ_ne_zero, ↓reduceIte, ← Finset.sum_div, hv', zero_div, add_zero]
  have ha2 : (∑ i : Fin (m + 1), spikeA (m + 1) i ^ 2) =
      1 + (∑ i : Fin (m + 1), spikeV (m + 1) i ^ 2) /
        (((m + 1 : ℕ) : ℝ)^2)^2 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [spikeA, spikeV, div_pow, Finset.sum_div]
  refine ⟨hv, hv2, spikeV_abs (m + 1) hn, ha, ?_⟩
  have hz (i : Fin (m + 1)) : spikeZ (m + 1) i ^ 2 =
      spikeA (m + 1) i ^ 2 - (2 / ((m + 1 : ℕ) : ℝ)) * spikeA (m + 1) i +
        (1 / ((m + 1 : ℕ) : ℝ))^2 := by unfold spikeZ; ring
  unfold spikeQ popMean mean
  simp_rw [hz]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ha, ha2, hv2]
  push_cast
  field_simp [hd, hn0, hm0]
  <;> ring

end
end AronowAudit.P005.Wave1.InteractedExpansion
