import AronowAudit.P029.P029_Audit

/-!
# P029-T23: the inside-log objective does not implement observation weights

The icsw 1.0.0 help's observation-weights claim is read with
`R/compliance.score.R` lines 88-91 (weights inside the logarithm), versus the Bernoulli
likelihood of equation (7), p. 497. The article's p. 498 bootstrap recommendation is not
refuted.
Witness: sixteen observations `(x, z, k) ∈ Bool × Bool × Fin 4`, success iff
`k < twoSidedSuccesses (x, z)` (cell success counts (1, 2, 1, 3)), weight 9 on successes and 1
on failures, parameter space `Theta` = ordered interior receipt probabilities
`0 < q(x,0) < q(x,1) < 1` (the feasible nested family; see `nested_receipt_parameters`).
The unweighted cell optimum `packageCells = (1/4, 1/2, 1/4, 3/4)` exactly minimizes the
package objective but not the weighted objective, which `weightedCells` strictly improves.
-/

namespace AronowAudit.P029.Wave1.PackageWeightedFit

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section


/-- Parameter space: ordered interior receipt probabilities `q(x, z)` for binary X and Z
(cell order `(x, z)`), i.e. the saturated nested Bernoulli family of equation (7). -/
abbrev Theta : Type :=
  {q : Bool × Bool → ℝ // ∀ x : Bool, 0 < q (x, false) ∧ q (x, false) < q (x, true) ∧ q (x, true) < 1}

/-- Observation index `(x, z, k)`, four observations per `(x, z)` cell. -/
abbrev Obs : Type := Bool × Bool × Fin 4

/-- Observed receipt: success iff `k < twoSidedSuccesses (x, z)`. -/
def obsD (i : Obs) : Bool := decide (i.2.2.val < twoSidedSuccesses (i.1, i.2.1))

/-- Bernoulli likelihood contribution of observation `i` at parameter `q`. -/
def lik (q : Theta) (i : Obs) : ℝ := bernoulliFactor (q.val (i.1, i.2.1)) (obsD i)

/-- Observation weights: 9 on successes, 1 on failures. -/
def obsW (i : Obs) : ℝ := if obsD i then 9 else 1

/-- Every likelihood contribution is positive at every parameter of `Theta`, and every weight is
positive (the antecedents of the printed claim). -/
def N1 : Prop := (∀ (q : Theta) (i : Obs), 0 < lik q i) ∧ ∀ i : Obs, 0 < obsW i

/-- The parameter with value `packageCells` exactly minimizes the package's inside-log objective over
`Theta`. Use `inside_log_minimizers` (reduces to the unit-weight objective) and
`saturated_weighted_objective_minimum` with unit weights, `cell i = (i.1, i.2.1)`,
`D = obsD` (cell totals `(n, 4 - n)`, `qhat = n/4 = packageCells`). -/
def N2 : Prop :=
  ∀ q : Theta, q.val = packageCells → IsMinimizer (fun t : Theta => packageObjective (lik t) obsW) q

/-- The parameter with value `packageCells` does not minimize the observation-weighted objective:
the feasible parameter with value `weightedCells` is strictly better
(`saturated_weighted_objective_minimum` with `obsW`: totals `(9n, 4 - n)`, `qhat =
weightedCells`, uniqueness since `packageCells ≠ weightedCells`; feasibility of
`weightedCells` is in `two_sided_weight_counterexample`). -/
def N3 : Prop :=
  ∀ q : Theta, q.val = packageCells →
    ¬ IsMinimizer (fun t : Theta => weightedObjective (lik t) obsW) q

/-- Feasibility of `packageCells`, the first conjunct of
`two_sided_weight_counterexample`. -/
def N4 : Prop := ∃ q : Theta, q.val = packageCells


end

end AronowAudit.P029.Wave1.PackageWeightedFit
