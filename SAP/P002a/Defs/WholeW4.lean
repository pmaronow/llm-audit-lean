import Mathlib
import SAP.P002a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P002a

universe u

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology

/-- P002-T7; Supplement p. 42 (Supplement PDF p. 22), Lemma 20, (E.58)-(E.61),
with the canonical correction of 2026-11-04.
Fix a positive covariate dimension and admissible constants. For any deterministic
strictly increasing sequence of models in Xi whose population OLS residual variance
is strictly positive in each arm at every size, and any fixed deterministic strict
subsequence, the following hold on one event of probability one, simultaneously for
all positive thresholds: the feasible and pooled-coefficient oracle reassignment
statistics merge relative to the oracle standard deviation (E.58); the oracle and
feasible statistics have standard normal absolute tails on that scale (E.59)-(E.60);
and the feasible variance estimator is ratio-consistent for the oracle reassignment
variance (corrected E.61).
The usual measure-theoretic conditions are assumed. Observed assignments have exact
measurable complete-randomization marginals with any coupling across sizes; the
conditional reassignment law holds the observed response fixed. Xi includes valid
designs with at least two units, monotone receipt, a nonempty complier set, centered
covariates and Assumption 5. OLS uses a fixed least-squares minimizer on singular
arms. Residual positivity is pointwise in size, with no uniform lower bound. No
finite-size positivity of the conditional oracle variance is assumed; the variance
quotient is zero at denominator zero, as with real division in Lean. -/
def T7WholeStatement_W4 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ n, CovPopulation (sizes n) k)
    (Z : ∀ n, Ω → Finset (Fin (sizes n))) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1 / 2) (hP : ∀ n, Xi (P n) δ e A B r)
    (hpositive : ∀ n a, 0 < popVar (residual (P n) a (late (P n).pop)))
    (hZ : RandomizationSequence (fun n => (P n).pop) μ Z)
    (sub : ℕ → ℕ) (hsub : StrictMono sub),
  ∀ᵐ ω ∂μ,
    (∀ κ : ℝ, 0 < κ → Tendsto (fun j =>
      let N := sub j
      let q := observedW (P N).pop (late (P N).pop) (Z N ω)
      probability (P N).pop (fun S => |adjustedTau (P N) q S - oracleStar (P N) q S| ≥
        κ * Real.sqrt (designVariance (P N).pop (oracleStar (P N) q)))) atTop (nhds 0)) ∧
    (∀ x : ℝ, 0 < x → Tendsto (fun j =>
      let N := sub j
      let q := observedW (P N).pop (late (P N).pop) (Z N ω)
      |probability (P N).pop (fun S => |oracleStar (P N) q S| ≥
        x * Real.sqrt (designVariance (P N).pop (oracleStar (P N) q))) - normalTail x|)
      atTop (nhds 0)) ∧
    (∀ x : ℝ, 0 < x → Tendsto (fun j =>
      let N := sub j
      let q := observedW (P N).pop (late (P N).pop) (Z N ω)
      |probability (P N).pop (fun S => |adjustedTau (P N) q S| ≥
        x * Real.sqrt (designVariance (P N).pop (oracleStar (P N) q))) - normalTail x|)
      atTop (nhds 0)) ∧
    (∀ κ : ℝ, 0 < κ → Tendsto (fun j =>
      let N := sub j
      let q := observedW (P N).pop (late (P N).pop) (Z N ω)
      probability (P N).pop (fun S => |adjustedSigma2 (P N) q S /
        designVariance (P N).pop (oracleStar (P N) q) - 1| ≥ κ)) atTop (nhds 0))

end
end SAP.P002a
