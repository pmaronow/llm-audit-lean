import AronowAudit.P005.Wave1.InteractedExpansion.N1

set_option autoImplicit false
namespace AronowAudit.P005.Wave1.InteractedExpansion
open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology
noncomputable section

/-- Bounds independent of the grid-moment node. -/
theorem spikeA_bounds (n : ℕ) (hn : 3 ≤ n) (i : Fin n) :
    -(1 / (n : ℝ)^2) ≤ spikeA n i ∧ spikeA n i ≤ 1 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (0 : ℝ) < (n : ℝ)^2 := by positivity
  have he : 1 / (n : ℝ)^2 ≤ 1 := (div_le_iff₀ hsq).2 (by nlinarith)
  by_cases hi : i.val = 0
  · simp only [spikeA, if_pos hi]
    constructor <;> linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hsq.le]
  · rw [spikeA, if_neg hi]
    have hv := abs_le.mp (spikeV_abs n hn i)
    constructor
    · simpa only [neg_div] using div_le_div_of_nonneg_right hv.1 hsq.le
    · exact (div_le_iff₀ hsq).2 (by nlinarith [hv.2])

theorem spikeA_injective (n : ℕ) (hn : 6 ≤ n) : Function.Injective (spikeA n) := by
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hd : (n : ℝ) - 2 ≠ 0 := by linarith
  have hord (i : Fin n) (hi : i.val ≠ 0) : spikeA n i < 1 := by
    rw [spikeA, if_neg hi]
    apply (div_lt_iff₀ (sq_pos_of_ne_zero hn0)).2
    have hv := (abs_le.mp (spikeV_abs n (by omega) i)).2
    nlinarith
  intro i j hij
  by_cases hi : i.val = 0
  · by_cases hj : j.val = 0
    · exact Fin.ext (hi.trans hj.symm)
    · have h := hord j hj
      rw [← hij, spikeA, if_pos hi] at h
      linarith
  · by_cases hj : j.val = 0
    · have h := hord i hi
      rw [hij, spikeA, if_pos hj] at h
      linarith
    · have hvEq : spikeV n i = spikeV n j := by
        apply (div_left_inj' (pow_ne_zero 2 hn0)).mp
        simpa only [spikeA, if_neg hi, if_neg hj] using hij
      have hgrid : 2 * ((i.val - 1 : ℕ) : ℝ) / ((n : ℝ) - 2) =
          2 * ((j.val - 1 : ℕ) : ℝ) / ((n : ℝ) - 2) := by
        simp only [spikeV, if_neg hi, if_neg hj] at hvEq
        linarith
      have hnum := (div_left_inj' hd).mp hgrid
      have hval : ((i.val - 1 : ℕ) : ℝ) = ((j.val - 1 : ℕ) : ℝ) := by linarith
      have hnat : i.val - 1 = j.val - 1 := by exact_mod_cast hval
      apply Fin.ext
      omega

theorem n5_proof : N5 := by
  intro n hn A hcard
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  have hdiff : spikeA n i ≠ spikeA n j := fun h => hij (spikeA_injective n hn h)
  have hex : ∃ k ∈ A, spikeA n k - mean A (spikeA n) ≠ 0 := by
    by_cases h : spikeA n i - mean A (spikeA n) = 0
    · refine ⟨j, hj, ?_⟩
      intro h'
      apply hdiff
      linarith
    · exact ⟨i, hi, h⟩
  have hsum : 0 < ∑ k ∈ A, (spikeA n k - mean A (spikeA n))^2 := by
    apply Finset.sum_pos' (fun k hk => sq_nonneg _)
    obtain ⟨k, hk, hne⟩ := hex
    exact ⟨k, hk, sq_pos_of_ne_zero hne⟩
  have hm : 0 < mean A (fun k => (spikeA n k - mean A (spikeA n))^2) :=
    div_pos hsum (by exact_mod_cast (show 0 < A.card by omega))
  rw [(mean_square_centering A hA (spikeA n)).1] at hm
  simpa only [sampleCov, pow_two] using hm

end
end AronowAudit.P005.Wave1.InteractedExpansion
