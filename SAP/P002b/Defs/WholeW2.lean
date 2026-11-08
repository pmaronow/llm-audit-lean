import Mathlib
import SAP.P002b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b

open scoped ENNReal
open Filter

/-- P002-T21; Supplement p. 39 (Supplement PDF p. 19), corrected display (E.36).
Fix positive covariate dimension, delta less than one, positive epsilon, A and B,
and a balance constant in (0, 1/2]. For every significance level alpha in (0, 1),
the ordinary right-hand limit at zero of the sample-size limit superior of the
nested suprema over LATE and Xi of adjusted-statistic rejection probabilities
exists in [0, 1] and is at most alpha. The cutoff is the standard-normal
(1-alpha/2)-quantile minus kappa. All positive population sizes are included;
empty model suprema are zero. Absolute studentization is zero for zero over zero
and infinity for a nonzero numerator over zero scale, and singular regression
arms use the fixed least-squares minimizer. The usual measure-theoretic
conditions are assumed. No positive population residual variance is required.
The corrected claim uses Xi and an inner limit superior; it asserts an ordinary
outer right-hand limit. -/
def T21WholeStatement : Prop :=
  ∀ (k : ℕ) (δ e A B r α : ℝ),
    0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
    (0 < r ∧ r ≤ 1 / 2) → (0 < α ∧ α < 1) →
    ∃ u : ℝ≥0∞,
      u ≤ 1 ∧
      Tendsto (fun κ : ℝ => Filter.limsup
        (fun n : ℕ => adjustedTailSupremum n k δ e A B r α κ) atTop)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds u) ∧
      u ≤ ENNReal.ofReal α

end SAP.P002b
