import Mathlib
import SAP.P031.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031

open scoped BigOperators Topology
open Finset Filter

noncomputable section

/-- P031-T5; pp. 367–368 (PDF pp. 3–4), including footnote 2.
Historical, uncredited result for the broader normality-only contract.
Neyman's finite randomization bias equals the
population variance of unit effects divided by N-1 and is nonnegative, but
normality alone does not imply the asserted conjunction of robust-variance
equivalences and conservative normal-interval coverages. There is a growing
population sequence with an exact-variance standardized normal limit on which
HR fails relative equivalence to HC2. This negates the conjunction of three
equivalences and five coverage assurances; it does not separately establish
interval undercoverage. The witness falls outside the cited regular regime
of the effective canonical claim. Growth means N tends to infinity;
normality means CDF convergence after centering at the population effect and
dividing by the actual standard deviation, with eventually positive variance.
Equivalence means relative error in probability, and conservative coverage means
an eventual lower bound of 2 Phi(z)-1-epsilon for every z>0 and epsilon>0.
HC1=N/(N-2) HR and HC3 uses squared leverage corrections. The usual
measure-theoretic conditions are assumed; no arm-growth or consistency
assumption is added. -/
def T5WholeStatement : Prop :=
  (∀ P : Population,
    expectation P.M (fun s => neymanEstimator P s) - trueVariance P =
      popVariance (fun i => P.y1 i - P.y0 i) / ((P.N : ℝ) - 1) ∧
    0 ≤ expectation P.M (fun s => neymanEstimator P s) - trueVariance P) ∧
  T5Statement

/-- P031-T6; Section 4, p. 369 (PDF p. 5).
Historical, uncredited result for the broader normality-only contract.
The OLS and constant-effects warning holds, with
unbalanced growing sequences giving both directions of variance error on the
N-times-variance scale and a standardized-normal sequence giving strict limiting
undercoverage for both estimators. However, the contrasting Neyman/HC2 coverage
assurance fails under normality alone. This witness falls outside the cited
regular regime of the effective canonical claim. There is an unbalanced growing
sequence with positive actual
variance in every row and an exact-variance standardized normal limit whose
Neyman and HC2 coverages at z=1 both tend to 1/2, strictly below 2 Phi(1)-1;
neither coverage is conservative in the eventual-lower-bound sense.
The usual measure-theoretic conditions are assumed. A fixed treatment arm is
permitted; no additional arm-growth, moment-growth, or consistency assumption
is imposed. The once-unhatted CE quantity is the imputation estimator. -/
def T6WholeStatement : Prop :=
  T6Statement ∧
  (1 / 2 : ℝ) < 2 * normalCDF 1 - 1 ∧
  ∃ P : ℕ → Population,
    GrowingPopulations P ∧
    (∀ n, (P n).N ≠ 2 * (P n).M) ∧
    (∀ n, 0 < trueVariance (P n)) ∧
    StandardizedNormalLimit P ∧
    Tendsto (fun n => coverage (P n) neymanEstimator 1) atTop (𝓝 (1 / 2)) ∧
    Tendsto (fun n => coverage (P n) hc2Estimator 1) atTop (𝓝 (1 / 2)) ∧
    ¬ ConservativeCoverage P neymanEstimator 1 ∧
    ¬ ConservativeCoverage P hc2Estimator 1

/-- Exact shift identities for every legal assignment, including individual
outcomes, both fitted coefficients, and every residual. -/
def FullShiftIdentities : Prop :=
  ∀ (P : Population) (c d : ℝ),
    groupMean univ (shiftedPopulation P c d).y0 = groupMean univ P.y0 + c ∧
    populationEffect (shiftedPopulation P c d) = populationEffect P + d ∧
    trueVariance (shiftedPopulation P c d) = trueVariance P ∧
    ∀ s ∈ (univ : Finset (Fin P.N)).powersetCard P.M,
      (∀ i, observed s (shiftedPopulation P c d).y1 (shiftedPopulation P c d).y0 i =
        observed s P.y1 P.y0 i + c + d * treatment s i) ∧
      intercept s (observed s (shiftedPopulation P c d).y1 (shiftedPopulation P c d).y0) =
        intercept s (observed s P.y1 P.y0) + c ∧
      pointEstimate (shiftedPopulation P c d) s = pointEstimate P s + d ∧
      (∀ i, residual s (observed s (shiftedPopulation P c d).y1
        (shiftedPopulation P c d).y0) i = residual s (observed s P.y1 P.y0) i) ∧
      olsEstimator (shiftedPopulation P c d) s = olsEstimator P s

/-- Row n is k=n+2, so n ranging over the naturals covers every integer k≥2.
The finite exact formulas hold for every real a; no ratio is used here. -/
def FootnoteExactRow (a : ℝ) (n : ℕ) : Prop :=
  let P := footnotePopulation a n
  (P.N : ℝ) * trueVariance P =
    (P.N : ℝ) / ((P.N : ℝ) - 1) * (3 * a ^ 2 + 2 * a + 1 / 3) ∧
  expectation P.M (fun s => groupMean s (footnoteSigns (n + 2)) ^ 2) =
    3 / ((P.N : ℝ) - 1) ∧
  ∀ s ∈ (univ : Finset (Fin P.N)).powersetCard P.M,
    (P.N : ℝ) * olsEstimator P s =
      (P.N : ℝ) / ((P.N : ℝ) - 2) *
        (4 * a ^ 2 / 3 + 4 - (4 * a ^ 2 / 3 + 4 / 9) *
          groupMean s (footnoteSigns (n + 2)) ^ 2)

/-- The exact actual variance, expected OLS estimate, and their ratio at k=2. -/
def FootnoteFiniteComparison (a v e q : ℝ) : Prop :=
  let P := footnotePopulation a 0
  0 < trueVariance P ∧ trueVariance P = v ∧
  expectation P.M (fun s => olsEstimator P s) = e ∧
  expectation P.M (fun s => olsEstimator P s) / trueVariance P = q

/-- P031-T10; counterexample to footnote 3, p. 369 (PDF p. 5), parts (a)–(c).
Shifting all control outcomes by c and all treatment outcomes by c+d shifts the
control mean and population effect by c and d. Assignment by assignment, it
adds c+dX to the observed vector, shifts the intercept and treatment estimate
by c and d, and preserves every residual, OLS variance estimate, and actual
randomization variance. For N=4k, M=k, k≥2, the balanced sign schedules
y0=z, y1=a z+2, a=1,2,1/2, share allocation 1/4, control mean 0 and effect 2.
Their moments and exact N-times-variance and OLS formulas hold, with the treated
sign mean r satisfying E[r²]=3/(N-1). Their true leading limits are 16/3,49/3,25/12,
their OLS probability and expectation limits are 16/3,28/3,13/3, and their
OLS/actual-variance probability-limit ratios are 1,4/7,52/25. At k=2 the printed
outcome vectors give 28 assignments, actual variances 16/21,7/3,25/84, expected
OLS estimates 16/21,8/7,2/3 and expectation/variance ratios 1,24/49,56/25.
Thus allocation and the two first moments do not determine the variance relation.
The usual measure-theoretic conditions are assumed. -/
def T10WholeStatement : Prop :=
  T10Statement ∧ FullShiftIdentities ∧
  (∀ (a : ℝ) (n : ℕ), FootnoteExactRow a n) ∧
  (footnotePopulation 1 0).N = 8 ∧ (footnotePopulation 1 0).M = 2 ∧
  ((univ : Finset (Fin 8)).powersetCard 2).card = 28 ∧
  (∀ a : ℝ, (footnotePopulation a 0).y0 = ![-1, -1, -1, -1, 1, 1, 1, 1]) ∧
  (footnotePopulation 1 0).y1 = ![1, 1, 1, 1, 3, 3, 3, 3] ∧
  (footnotePopulation 2 0).y1 = ![0, 0, 0, 0, 4, 4, 4, 4] ∧
  (footnotePopulation (1 / 2) 0).y1 = ![3/2, 3/2, 3/2, 3/2, 5/2, 5/2, 5/2, 5/2] ∧
  FootnoteFiniteComparison 1 (16 / 21) (16 / 21) 1 ∧
  FootnoteFiniteComparison 2 (7 / 3) (8 / 7) (24 / 49) ∧
  FootnoteFiniteComparison (1 / 2) (25 / 84) (2 / 3) (56 / 25)

end
end SAP.P031
