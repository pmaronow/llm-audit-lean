import Mathlib
import SAP.P020.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P020

open scoped BigOperators

/-- P020-T3; p. 61 (PDF p. 23); definition of n_j on p. 44 (PDF p. 6).
The printed logistic link is strictly increasing, and the raw-count treatment
shift 2/5 - (9/10)n is at most -1/2 for every real n at least one. Consequently
every individual probability contrast and every finite nonempty average contrast
is negative, excluding the reported 7/1000, for arbitrary real control predictors
and sizes at least one. The scalar instance N = 1, n = 1, control predictor zero
has control probability 1/2 and treated probability L(-1/2) < 1/2.
The usual measure-theoretic conditions are assumed; the displayed quantities are
finite real expressions. The scalar instance specifies no randomized cluster
design. -/
def T3WholeStatement_W2 : Prop :=
  (StrictMono logistic) ∧
  (∀ (n : ℝ), 1 ≤ n →
    (2 : ℝ) / 5 - (9 : ℝ) / 10 * n ≤ -(1 : ℝ) / 2) ∧
  (∀ (base n : ℝ), 1 ≤ n →
    logistic (base + (2 : ℝ) / 5 - (9 : ℝ) / 10 * n) - logistic base < 0) ∧
  (∀ (N : ℕ), 0 < N → ∀ (base size : Fin N → ℝ),
    (∀ i, 1 ≤ size i) →
    (∑ i : Fin N, (logistic (base i + 2 / 5 - 9 / 10 * size i) -
      logistic (base i))) / (N : ℝ) < 0) ∧
  (∀ (N : ℕ), 0 < N → ∀ (base size : Fin N → ℝ),
    (∀ i, 1 ≤ size i) →
    (∑ i : Fin N, (logistic (base i + 2 / 5 - 9 / 10 * size i) -
      logistic (base i))) / (N : ℝ) ≠ (7 : ℝ) / 1000) ∧
  (logistic 0 = (1 : ℝ) / 2 ∧
    logistic ((0 : ℝ) + 2 / 5 - 9 / 10 * 1) = logistic (-(1 : ℝ) / 2) ∧
    logistic (-(1 : ℝ) / 2) < (1 : ℝ) / 2)

end SAP.P020
