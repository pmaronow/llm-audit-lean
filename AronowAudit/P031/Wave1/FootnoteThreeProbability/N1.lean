import AronowAudit.P031.Wave1.FootnoteThreeProbabilityBlueprint

namespace AronowAudit.P031.Wave1.FootnoteThreeProbability
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

/-- The sample-variance error is controlled by the two raw-moment errors. -/
theorem n1_proof : N1 := by
  classical
  intro N M v B s hM hs hB hv
  have hMN : M ≤ N := by
    simpa only [hs, Fintype.card_fin] using (Finset.card_le_univ s)
  have hmR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hnR : (2 : ℝ) ≤ N := by exact_mod_cast (hM.trans hMN)
  have hm : (M : ℝ) ≠ 0 := by linarith
  have hm1 : 0 < (M : ℝ) - 1 := by linarith
  have hsc : (s.card : ℝ) ≠ 0 := by simpa only [hs] using hm
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn : (Fintype.card (Fin N) : ℝ) ≠ 0 := by
    simpa only [Fintype.card_fin] using hn0
  have hmean : ∀ t : Finset (Fin N), 0 < (t.card : ℝ) → |groupMean t v| ≤ B := by
    intro t ht
    unfold groupMean
    rw [abs_div, abs_of_pos ht]
    apply (div_le_iff₀ ht).mpr
    calc
      |∑ i ∈ t, v i| ≤ ∑ i ∈ t, |v i| := Finset.abs_sum_le_sum_abs v t
      _ ≤ ∑ _i ∈ t, B := Finset.sum_le_sum (fun i _ => hv i)
      _ = B * (t.card : ℝ) := by simp [mul_comm]
  let μ := groupMean (Finset.univ : Finset (Fin N)) v
  let μs := groupMean s v
  let ν := groupMean (Finset.univ : Finset (Fin N)) (fun i => v i ^ 2)
  let νs := groupMean s (fun i => v i ^ 2)
  have hμ : |μ| ≤ B := hmean Finset.univ (by simpa using (show (0 : ℝ) < N by linarith))
  have hμs : |μs| ≤ B := hmean s (by rw [hs]; linarith)
  have hsq : |μs ^ 2 - μ ^ 2| ≤ 2 * B * |μs - μ| := by
    calc
      |μs ^ 2 - μ ^ 2| = |μs - μ| * |μs + μ| := by
        rw [show μs ^ 2 - μ ^ 2 = (μs - μ) * (μs + μ) by ring, abs_mul]
      _ ≤ |μs - μ| * (|μs| + |μ|) :=
        mul_le_mul_of_nonneg_left (abs_add_le μs μ) (abs_nonneg _)
      _ ≤ |μs - μ| * (B + B) :=
        mul_le_mul_of_nonneg_left (add_le_add hμs hμ) (abs_nonneg _)
      _ = 2 * B * |μs - μ| := by ring
  have hvar : 0 ≤ popVariance v := by
    unfold popVariance
    exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Nat.cast_nonneg _)
  have hvarB : popVariance v ≤ B ^ 2 :=
    bounded_population_variance v B hB (by simp only [Fintype.card_fin]; linarith) hv
  have hid : sampleVariance s v - popVariance v =
      (M : ℝ) / ((M : ℝ) - 1) * ((νs - ν) - (μs ^ 2 - μ ^ 2)) +
        popVariance v / ((M : ℝ) - 1) := by
    dsimp only [νs, ν, μs, μ]
    unfold sampleVariance
    rw [group_sse_raw s v hsc]
    simp only [pop_variance_raw v hn, groupMean, hs, Finset.card_univ, Fintype.card_fin]
    field_simp [hm, hm1.ne', hn0] <;> ring
  have ha : 0 ≤ (M : ℝ) / ((M : ℝ) - 1) := div_nonneg (by positivity) hm1.le
  have ha2 : (M : ℝ) / ((M : ℝ) - 1) ≤ 2 :=
    (div_le_iff₀ hm1).mpr (by linarith)
  have herr : |(νs - ν) - (μs ^ 2 - μ ^ 2)| ≤ |νs - ν| + 2 * B * |μs - μ| := by
    calc
      _ ≤ |νs - ν| + |μs ^ 2 - μ ^ 2| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (νs - ν) 0 (μs ^ 2 - μ ^ 2))
      _ ≤ _ := add_le_add le_rfl hsq
  change |sampleVariance s v - popVariance v| ≤
    2 * |νs - ν| + 4 * B * |μs - μ| + B ^ 2 / ((M : ℝ) - 1)
  calc
    _ = |(M : ℝ) / ((M : ℝ) - 1) * ((νs - ν) - (μs ^ 2 - μ ^ 2)) +
        popVariance v / ((M : ℝ) - 1)| := congrArg abs hid
    _ ≤ |(M : ℝ) / ((M : ℝ) - 1) * ((νs - ν) - (μs ^ 2 - μ ^ 2))| +
        |popVariance v / ((M : ℝ) - 1)| := abs_add_le _ _
    _ = (M : ℝ) / ((M : ℝ) - 1) * |(νs - ν) - (μs ^ 2 - μ ^ 2)| +
        popVariance v / ((M : ℝ) - 1) := by
      rw [abs_mul, abs_of_nonneg ha, abs_div, abs_of_nonneg hvar, abs_of_pos hm1]
    _ ≤ (M : ℝ) / ((M : ℝ) - 1) * (|νs - ν| + 2 * B * |μs - μ|) +
        B ^ 2 / ((M : ℝ) - 1) :=
      add_le_add (mul_le_mul_of_nonneg_left herr ha)
        (div_le_div_of_nonneg_right hvarB hm1.le)
    _ ≤ 2 * (|νs - ν| + 2 * B * |μs - μ|) + B ^ 2 / ((M : ℝ) - 1) :=
      add_le_add (mul_le_mul_of_nonneg_right ha2
        (show 0 ≤ |νs - ν| + 2 * B * |μs - μ| by positivity)) le_rfl
    _ = _ := by ring

end
end AronowAudit.P031.Wave1.FootnoteThreeProbability
