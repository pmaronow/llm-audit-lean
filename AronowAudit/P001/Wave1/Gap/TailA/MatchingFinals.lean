import AronowAudit.P001.Wave1.Lib.TailA.MatchingEndpoints

/-! Matching-bootstrap counterexamples, corrections, and refutations of universal assurances. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open AronowAudit.P001.TailA

namespace AronowAudit.P001.Wave1.TailA

universe u

/-- Hot deck in the explicit uniform-score, Bernoulli-response, independent sign-noise design is exactly unbiased. Its sampling variance multiplied by `n` has a positive limit, while its bootstrap variance multiplied by `n` has a smaller limiting expectation and does not converge in probability to that positive limit.
Target P001-T14: Footnote 15, corrected: for hot deck (nearest-neighbour) imputation the ordinary bootstrap can give inconsistent standard errors even without bias.
Location: p. 233 (PDF p. 251), footnote 15; Table 6.3.1, row 'Hot Deck Imputation'. -/
theorem hot_deck_bootstrap_counterexample_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (Z : ℕ → Ω → ℝ × Bool × Bool)
      (hiid : IID μ Z)
      (hlaw : μ.map (Z 0) = matchingUnitLaw),
      MatchingFailure μ Z false) := by
  intro Ω _ μ _ Z hiid hlaw
  exact (matching_failure_both μ Z hiid hlaw).1

theorem hot_deck_bootstrap_correction_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (Z : ℕ → Ω → ℝ × Bool × Bool)
      (hiid : IID μ Z)
      (hlaw : μ.map (Z 0) = matchingUnitLaw),
      MatchingFailure μ Z false) := by
  intro Ω _ μ _ Z hiid hlaw
  exact (matching_failure_both μ Z hiid hlaw).1

/-- Causal nearest-neighbor matching in the explicit uniform-score, Bernoulli-response, independent sign-noise design is exactly unbiased. Its sampling variance multiplied by `n` has a positive limit, while its bootstrap variance multiplied by `n` has a smaller limiting expectation and does not converge in probability to that positive limit.
Target P001-T16: Section 7.2.4 and footnote 20, corrected: for nearest-neighbour matching the ordinary bootstrap can give inconsistent standard errors even without bias, and root-$n$ consistency and bootstrap validity are separate questions.
Location: p. 264 (PDF p. 282), end of Section 7.2.4 and footnote 13; p. 279 (PDF p. 297), footnote 20. -/
theorem matching_bootstrap_counterexample_supporting_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (Z : ℕ → Ω → ℝ × Bool × Bool)
      (hiid : IID μ Z)
      (hlaw : μ.map (Z 0) = matchingUnitLaw),
      MatchingFailure μ Z true) := by
  intro Ω _ μ _ Z hiid hlaw
  exact (matching_failure_both μ Z hiid hlaw).2

theorem matching_bootstrap_correction_supporting_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (Z : ℕ → Ω → ℝ × Bool × Bool)
      (hiid : IID μ Z)
      (hlaw : μ.map (Z 0) = matchingUnitLaw),
      MatchingFailure μ Z true) := by
  intro Ω _ μ _ Z hiid hlaw
  exact (matching_failure_both μ Z hiid hlaw).2

/-- The nearest-neighbor causal matching statistic with a consistent score recomputed on each sample and bootstrap resample is unbiased. Its sampling variance multiplied by `n` has a finite positive limit, while its bootstrap variance multiplied by `n` does not converge in probability to that limit.
Target P001-T16: Section 7.2.4 and footnote 20, corrected: for nearest-neighbour matching the ordinary bootstrap can give inconsistent standard errors even without bias, and root-$n$ consistency and bootstrap validity are separate questions.
Location: p. 264 (PDF p. 282), end of Section 7.2.4 and footnote 13; p. 279 (PDF p. 297), footnote 20. -/
theorem estimated_matching_bootstrap_failure_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (Z : ℕ → Ω → ℝ × Bool × Bool)
      (hiid : IID μ Z)
      (hlaw : μ.map (Z 0)=matchingUnitLaw),
      (∀ n,0 < n → mean μ (fun ω => causalMatchEstimated (firstSample Z n ω))=0) ∧
   Tendsto (fun (n : ℕ) => (n : ℝ)*var μ (fun ω => causalMatchEstimated (firstSample Z n ω))) atTop (nhds matchV) ∧
   Tendsto (fun (n : ℕ) => mean μ (fun ω => (n : ℝ)*bootVar causalMatchEstimated (firstSample Z n ω))) atTop (nhds matchVB) ∧
   0 < matchVB ∧ matchVB < matchV ∧
   ¬ CP μ (fun n ω => (n : ℝ)*bootVar causalMatchEstimated (firstSample Z n ω)) matchV) := by
  intro Ω _ μ _ Z hiid hlaw
  simpa only [MatchingFailure,ite_true,estimated_matching_statistic_equal,bootVar,bootMean]
    using (matching_failure_both μ Z hiid hlaw).2

theorem matching_bootstrap_counterexample_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (Z : ℕ → Ω → ℝ × Bool × Bool)
      (hiid : IID μ Z)
      (hlaw : μ.map (Z 0)=matchingUnitLaw),
      (∀ n,0 < n → mean μ (fun ω => causalMatchEstimated (firstSample Z n ω))=0) ∧
   Tendsto (fun (n : ℕ) => (n : ℝ)*var μ (fun ω => causalMatchEstimated (firstSample Z n ω))) atTop (nhds matchV) ∧
   Tendsto (fun (n : ℕ) => mean μ (fun ω => (n : ℝ)*bootVar causalMatchEstimated (firstSample Z n ω))) atTop (nhds matchVB) ∧
   0 < matchVB ∧ matchVB < matchV ∧
   ¬ CP μ (fun n ω => (n : ℝ)*bootVar causalMatchEstimated (firstSample Z n ω)) matchV) :=
  estimated_matching_bootstrap_failure_final

theorem matching_bootstrap_correction_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (Z : ℕ → Ω → ℝ × Bool × Bool)
      (hiid : IID μ Z)
      (hlaw : μ.map (Z 0)=matchingUnitLaw),
      (∀ n,0 < n → mean μ (fun ω => causalMatchEstimated (firstSample Z n ω))=0) ∧
   Tendsto (fun (n : ℕ) => (n : ℝ)*var μ (fun ω => causalMatchEstimated (firstSample Z n ω))) atTop (nhds matchV) ∧
   Tendsto (fun (n : ℕ) => mean μ (fun ω => (n : ℝ)*bootVar causalMatchEstimated (firstSample Z n ω))) atTop (nhds matchVB) ∧
   0 < matchVB ∧ matchVB < matchV ∧
   ¬ CP μ (fun n ω => (n : ℝ)*bootVar causalMatchEstimated (firstSample Z n ω)) matchV) :=
  estimated_matching_bootstrap_failure_final


end AronowAudit.P001.Wave1.TailA
