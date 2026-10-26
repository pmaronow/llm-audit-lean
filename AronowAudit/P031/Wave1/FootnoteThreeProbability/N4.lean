import AronowAudit.P031.Wave1.FootnoteThreeProbabilityBlueprint

namespace AronowAudit.P031.Wave1.FootnoteThreeProbability
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

/-- Both arms have vanishing mean absolute sample-variance error. -/
theorem n4_proof : N4 := by
  classical
  intro hL1 P hN p hp hp1 hAlloc hBounded
  obtain ⟨B, hB⟩ := hBounded
  let C : ℝ := max B 1
  have hC : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right B 1)
  have hBC : B ≤ C := le_max_left B 1
  have hNr : Tendsto (fun n => ((P n).N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hN0 : ∀ n, ((P n).N : ℝ) ≠ 0 := by
    intro n
    have hn4 : (4 : ℝ) ≤ (P n).N := by exact_mod_cast (population_sizes (P n)).2.2.2
    linarith
  have hMr : Tendsto (fun n => ((P n).M : ℝ)) atTop atTop := by
    apply (hNr.atTop_mul_pos hp hAlloc).congr
    intro n
    field_simp [hN0 n] <;> ring
  have hComp : Tendsto (fun n => 1 - ((P n).M : ℝ) / (P n).N)
      atTop (nhds (1 - p)) := tendsto_const_nhds.sub hAlloc
  have hKr : Tendsto (fun n => (((P n).N - (P n).M : ℕ) : ℝ)) atTop atTop := by
    apply (hNr.atTop_mul_pos (by linarith : 0 < 1 - p) hComp).congr
    intro n
    rw [Nat.cast_sub (population_sizes (P n)).2.2.1]
    field_simp [hN0 n] <;> ring
  -- A single argument works for either deterministic arm-size sequence.
  have hOneArm : ∀ (m : ℕ → ℕ), (∀ n, 2 ≤ m n) → (∀ n, m n ≤ (P n).N) →
      Tendsto (fun n => (m n : ℝ)) atTop atTop →
      ∀ v : (n : ℕ) → Fin (P n).N → ℝ, (∀ n i, |v n i| ≤ C) →
      Tendsto (fun n => expectation (m n)
        (fun s => |sampleVariance s (v n) - popVariance (v n)|)) atTop (nhds 0) := by
    intro m hm hmn hmTop v hv
    let f : ℕ → ℝ := fun n => (((P n).N : ℝ) - m n) /
      ((m n : ℝ) * (((P n).N : ℝ) - 1))
    have hf0 : ∀ n, 0 ≤ f n := by
      intro n
      have hm2 : (2 : ℝ) ≤ m n := by exact_mod_cast hm n
      have hmnR : (m n : ℝ) ≤ (P n).N := by exact_mod_cast hmn n
      dsimp only [f]
      exact div_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have hf1 : ∀ n, f n ≤ 1 / (m n : ℝ) := by
      intro n
      have hm2 : (2 : ℝ) ≤ m n := by exact_mod_cast hm n
      have hmnR : (m n : ℝ) ≤ (P n).N := by exact_mod_cast hmn n
      have hmpos : (0 : ℝ) < m n := by linarith
      have hn1 : 0 < ((P n).N : ℝ) - 1 := by linarith
      calc
        f n ≤ (((P n).N : ℝ) - 1) / ((m n : ℝ) * (((P n).N : ℝ) - 1)) :=
          div_le_div_of_nonneg_right (by linarith) (mul_pos hmpos hn1).le
        _ = 1 / (m n : ℝ) := by field_simp [hmpos.ne', hn1.ne'] <;> ring
    have hfTop : Tendsto f atTop (nhds (0 : ℝ)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hmTop.const_div_atTop 1) hf0 hf1
    have hsqrt : Tendsto (fun n => Real.sqrt (f n)) atTop (nhds (0 : ℝ)) := by
      simpa only [Real.sqrt_zero] using hfTop.sqrt
    have hmMinus : Tendsto (fun n => (m n : ℝ) - 1) atTop atTop := by
      simpa only [sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-1 : ℝ) hmTop
    have hUpper : Tendsto (fun n => 6 * C ^ 2 * Real.sqrt (f n) +
        C ^ 2 / ((m n : ℝ) - 1)) atTop (nhds (0 : ℝ)) := by
      simpa only [mul_zero, add_zero] using
        (hsqrt.const_mul (6 * C ^ 2)).add (hmMinus.const_div_atTop (C ^ 2))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
    · intro n
      exact expectation_nonneg _ _ (fun s _ => abs_nonneg _)
    · intro n
      exact hL1 (P n).N (m n) (v n) C (hm n) (hmn n) hC (hv n)
  have hTreated := hOneArm (fun n => (P n).M)
    (fun n => (population_sizes (P n)).1) (fun n => (population_sizes (P n)).2.2.1)
    hMr (fun n => (P n).y1) (fun n i => ((hB n i).1).trans hBC)
  have hControl := hOneArm (fun n => (P n).N - (P n).M)
    (fun n => (population_sizes (P n)).2.1) (fun n => Nat.sub_le _ _)
    hKr (fun n => (P n).y0) (fun n i => ((hB n i).2).trans hBC)
  have hControl' : Tendsto (fun n => expectation (P n).M
      (fun s => |sampleVariance sᶜ (P n).y0 - popVariance (P n).y0|))
      atTop (nhds (0 : ℝ)) := by
    apply hControl.congr
    intro n
    symm
    simpa only [Fintype.card_fin] using
      (expectation_compl (P n).M
        (by simpa only [Fintype.card_fin] using (population_sizes (P n)).2.2.1)
        (fun s => |sampleVariance s (P n).y0 - popVariance (P n).y0|))
  constructor
  · apply probability_limit_of_mean_absolute_error
    simpa only [sub_zero] using hTreated
  · apply probability_limit_of_mean_absolute_error
    simpa only [sub_zero] using hControl'

end
end AronowAudit.P031.Wave1.FootnoteThreeProbability
