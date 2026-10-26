import AronowAudit.P008.P008_Audit

noncomputable section
namespace AronowAudit.P008

/-- Refutation of the printed interpolated-percentile calibration assertion. -/
theorem printed_percentile_calibration_refuted :
    ¬ (∀ {n : ℕ}
    (s : Fin (n + 1) → ℝ) (hs : Monotone s) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1),
    (uniformLaw (Fin (n + 1))).prob (fun k =>
      outside (quantile7 s (δ / 2)) (quantile7 s (1 - δ / 2)) (s k)) ≤ δ) := by
  intro h
  have hm : Monotone percentileExample := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [percentileExample] at *
  have hb := h percentileExample hm (1/20) (by norm_num) (by norm_num)
  norm_num only [show (1/20 : ℝ)/2 = 1/40 by norm_num,
    show 1-(1/20 : ℝ)/2 = 39/40 by norm_num] at hb
  rw [interpolated_percentile_counterexample.2.1,
    interpolated_percentile_counterexample.2.2.1,
    interpolated_percentile_counterexample.2.2.2.1] at hb
  norm_num at hb

/-- Refutation of the printed claim that a sum of probability differences
is itself a probability difference. -/
theorem printed_sum_probability_gloss_refuted :
    ¬ (∀ {J : ℕ} (q₀ q₁ : Fin J → ℝ)
    (h₀ : ∀ j, 0 ≤ q₀ j ∧ q₀ j ≤ 1) (h₁ : ∀ j, 0 ≤ q₁ j ∧ q₁ j ≤ 1),
    ∃ Q₀ Q₁ : ℝ, 0 ≤ Q₀ ∧ Q₀ ≤ 1 ∧ 0 ≤ Q₁ ∧ Q₁ ≤ 1 ∧
      Q₁ - Q₀ = ∑ j, (q₁ j - q₀ j)) := by
  intro h
  obtain ⟨q0,q1,h0,h0',h1,h1',he⟩ := h (fun _ : Fin 4 => 1) (fun _ => 0)
    (by intro j; norm_num) (by intro j; norm_num)
  norm_num at he
  linarith

end AronowAudit.P008

