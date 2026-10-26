import AronowAudit.P031.Wave1.FootnoteThreeCompleteBlueprint
import AronowAudit.P031.Wave1.FootnoteThreeProbability

namespace AronowAudit.P031.Wave1
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

/-- The deterministic, stochastic, and shift-invariance clauses of corrected footnote 3. -/
theorem footnote_three_complete :
  ∀ (P : ℕ → Population), GrowingPopulations P →
    ∀ (p v1 v0 c : ℝ), 0 < p → p < 1 →
    Tendsto (fun n => ((P n).M : ℝ) / (P n).N) atTop (nhds p) →
    Tendsto (fun n => popVariance (P n).y1) atTop (nhds v1) →
    Tendsto (fun n => popVariance (P n).y0) atTop (nhds v0) →
    Tendsto (fun n => popCovariance (P n).y1 (P n).y0) atTop (nhds c) →
    Tendsto (fun n => ((P n).N : ℝ) * trueVariance (P n)) atTop
      (nhds ((1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c)) ∧
    Tendsto (fun n => ((P n).N : ℝ) *
      expectation (P n).M (fun s => olsEstimator (P n) s)) atTop
      (nhds (v1 / (1 - p) + v0 / p)) ∧
    Tendsto (fun n => ((P n).N : ℝ) *
      (expectation (P n).M (fun s => olsEstimator (P n) s) - trueVariance (P n)))
      atTop (nhds ((2 * p - 1) * (v1 - v0) / (p * (1 - p)) + v1 + v0 - 2 * c)) ∧
    Tendsto (fun n => popVariance (fun i => (P n).y1 i - (P n).y0 i)) atTop
      (nhds (v1 + v0 - 2 * c)) ∧
    ((ArmSecondMomentsConverge P ∨ UniformlyBoundedOutcomes P) →
      ConvergesInProbability P (fun Q s => (Q.N : ℝ) * olsEstimator Q s)
        (v1 / (1 - p) + v0 / p) ∧
      (0 < (1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c →
        ConvergesInProbability P (fun Q s => olsEstimator Q s / trueVariance Q)
          ((v1 / (1 - p) + v0 / p) / ((1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c)))) ∧
    (∀ c' d : ℝ, ∀ n : ℕ,
      let Q := shiftedPopulation (P n) c' d
      groupMean Finset.univ Q.y0 = groupMean Finset.univ (P n).y0 + c' ∧
      populationEffect Q = populationEffect (P n) + d ∧
      trueVariance Q = trueVariance (P n) ∧
      ∀ s ∈ (Finset.univ : Finset (Fin (P n).N)).powersetCard (P n).M,
        olsEstimator Q s = olsEstimator (P n) s) := by
  exact FootnoteThreeComplete.assemble footnote_three_probability_complete

end
end AronowAudit.P031.Wave1
