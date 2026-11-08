import SAP.P031.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031

open scoped BigOperators Matrix Topology
open Finset Filter

noncomputable section

def T5Statement : Prop :=
    (∃ P : ℕ → Population,
      GrowingPopulations P ∧ StandardizedNormalLimit P ∧
      ¬ FirstOrderEquivalent P hrEstimator hc2Estimator) ∧
    ¬ (∀ P : ℕ → Population,
      GrowingPopulations P → StandardizedNormalLimit P →
      FirstOrderEquivalent P hrEstimator hc2Estimator ∧
      FirstOrderEquivalent P hc1Estimator hc2Estimator ∧
      FirstOrderEquivalent P hc3Estimator hc2Estimator ∧
      ∀ z : ℝ, 0 < z →
        ConservativeCoverage P neymanEstimator z ∧
        ConservativeCoverage P hc2Estimator z ∧
        ConservativeCoverage P hrEstimator z ∧
        ConservativeCoverage P hc1Estimator z ∧
        ConservativeCoverage P hc3Estimator z)

def T6Statement : Prop :=
    (∃ (P : ℕ → Population) (a v : ℝ), UnbalancedVarianceLimit P a v ∧ a < v ∧
      StandardizedNormalLimit P ∧ ∀ z : ℝ, 0 < z →
        ∃ q : ℝ, q < 2 * normalCDF z - 1 ∧
          Tendsto (fun r => coverage (P r) olsEstimator z) atTop (𝓝 q) ∧
          Tendsto (fun r => coverage (P r) ceEstimator z) atTop (𝓝 q)) ∧
    (∃ (P : ℕ → Population) (a v : ℝ), UnbalancedVarianceLimit P a v ∧ v < a)

def T10Statement : Prop :=
    FootnoteVarianceWitness 1 1 ∧ FootnoteVarianceWitness 2 (4 / 7) ∧
    FootnoteVarianceWitness (1 / 2) (52 / 25) ∧
    (4 / 7 : ℝ) ≠ 52 / 25 ∧
    ∀ (P : Population) (c d : ℝ),
      groupMean univ (shiftedPopulation P c d).y0 = groupMean univ P.y0 + c ∧
      populationEffect (shiftedPopulation P c d) = populationEffect P + d ∧
      trueVariance (shiftedPopulation P c d) = trueVariance P ∧
      ∀ s ∈ (univ : Finset (Fin P.N)).powersetCard P.M,
        olsEstimator (shiftedPopulation P c d) s = olsEstimator P s

def T11Statement : Prop :=
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
    (UniformlyBoundedOutcomes P → ArmSecondMomentsConverge P) ∧
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

end
end SAP.P031
