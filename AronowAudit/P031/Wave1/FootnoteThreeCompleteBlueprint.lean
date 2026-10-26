import AronowAudit.P031.Wave1.FootnoteThreeProbabilityBlueprint

/-!
# P031-T11: the complete corrected footnote 3

The complete corrected footnote 3 (p. 369) combines deterministic
and expectation limits with stochastic limits under an additional sample
condition, positivity of the leading true variance for the ratio, and exact
first-moment shift invariance for every row and every assignment.
-/

namespace AronowAudit.P031.Wave1.FootnoteThreeComplete
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

/-- Deterministic and stochastic limits, and exact shift invariance, for corrected footnote 3. -/
def Target : Prop :=
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
        olsEstimator Q s = olsEstimator (P n) s)

/-- The stochastic clauses of corrected footnote 3. -/
def N1 : Prop := FootnoteThreeProbability.Target

/-- The auxiliary statements imply the target. -/
theorem assemble (h1 : N1) : Target := by
  intro P hN p v1 v0 c hp hp1 hAlloc hV1 hV0 hCov
  obtain ⟨ht, he, hd, hv⟩ :=
    corrected_footnote_three_limits P hN p v1 v0 c hp hp1 hAlloc hV1 hV0 hCov
  refine ⟨ht, he, hd, hv, (h1 P hN p v1 v0 c hp hp1 hAlloc hV1 hV0 hCov).2, ?_⟩
  intro c' d n
  have hi := population_shift_invariance (P n) c' d
  exact ⟨hi.1, hi.2.1, hi.2.2.1, fun s hs => (hi.2.2.2 s hs).2.2.2⟩

end
end AronowAudit.P031.Wave1.FootnoteThreeComplete
