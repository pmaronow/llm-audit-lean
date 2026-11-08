import AronowAudit.P029.P029_Audit

/-!
# Wave1 blueprint: P029-T23, `AronowAudit.P029.printed_package_weighted_fit` (refute)

Target of the record: the icsw 1.0.0 help's observation-weights contract read with
`R/compliance.score.R` lines 88-91 (weights inside the logarithm), versus the Bernoulli
likelihood of equation (7), p. 497. The article's p. 498 bootstrap recommendation is not
refuted. Resolution: `refute`.
Witness (mapper record 5): sixteen observations `(x, z, k) ∈ Bool × Bool × Fin 4`, success iff
`k < twoSidedSuccesses (x, z)` (cell success counts (1, 2, 1, 3)), weight 9 on successes and 1
on failures, parameter space `Theta` = ordered interior receipt probabilities
`0 < q(x,0) < q(x,1) < 1` (the feasible nested family; see `nested_receipt_parameters`).
The unweighted cell optimum `packageCells = (1/4, 1/2, 1/4, 3/4)` exactly minimizes the
package objective but not the weighted objective, which `weightedCells` strictly improves.

`Target` is the negation of the universe-0 instance of the held contract (checked by `rfl`).
Final theorem (writers): `AronowAudit.P029.Wave1.printed_package_weighted_fit_refuted`
in `AronowAudit/P029/Wave1/PackageWeightedFit.lean`.
-/

namespace AronowAudit.P029.Wave1.PackageWeightedFit

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

/-- The frozen final statement: the negation of the printed contract
`printed_package_weighted_fit` (universe-0 instance). -/
def Target : Prop :=
  ¬ (∀ {I Θ : Type} [Fintype I] (L : Θ → I → ℝ) (w : I → ℝ), (∀ θ i, 0 < L θ i) →
      (∀ i, 0 < w i) → ∀ (θ : Θ), IsMinimizer (fun t => packageObjective (L t) w) θ →
        IsMinimizer (fun t => weightedObjective (L t) w) θ)

/-- Fidelity check: `Target` is literally the negation of the held declaration's statement. -/
theorem target_eq_negated_printed :
    Target = ¬ (type_of% @AronowAudit.P029.printed_package_weighted_fit.{0, 0}) := rfl

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

/-- **Node R5-N1** (`sixteen_row_positivity`; mapper record 5, paper-proof step 1). Every
likelihood contribution is positive at every parameter of `Theta`, and every weight is
positive (the antecedents of the printed contract). -/
def N1 : Prop := (∀ (q : Theta) (i : Obs), 0 < lik q i) ∧ ∀ i : Obs, 0 < obsW i

/-- **Node R5-N2** (`package_cells_are_exact_minimizer`; mapper record 5, step 2). The
parameter with value `packageCells` exactly minimizes the package's inside-log objective over
`Theta`. Use `inside_log_minimizers` (reduces to the unit-weight objective) and
`saturated_weighted_objective_minimum` with unit weights, `cell i = (i.1, i.2.1)`,
`D = obsD` (cell totals `(n, 4 - n)`, `qhat = n/4 = packageCells`). -/
def N2 : Prop :=
  ∀ q : Theta, q.val = packageCells → IsMinimizer (fun t : Theta => packageObjective (lik t) obsW) q

/-- **Node R5-N3** (`weighted_cells_strict_improvement`; mapper record 5, step 3). The
parameter with value `packageCells` does not minimize the observation-weighted objective:
the feasible parameter with value `weightedCells` is strictly better
(`saturated_weighted_objective_minimum` with `obsW`: totals `(9n, 4 - n)`, `qhat =
weightedCells`, uniqueness since `packageCells ≠ weightedCells`; feasibility of
`weightedCells` is in `two_sided_weight_counterexample`). -/
def N3 : Prop :=
  ∀ q : Theta, q.val = packageCells →
    ¬ IsMinimizer (fun t : Theta => weightedObjective (lik t) obsW) q

/-- **Node R5-N4** (feasibility of `packageCells`; trivial, proved in its node file from
`two_sided_weight_counterexample`). -/
def N4 : Prop := ∃ q : Theta, q.val = packageCells

/-- The nodes suffice. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) : Target := by
  intro h
  obtain ⟨q, hq⟩ := h4
  exact h3 q hq (h lik obsW h1.1 h1.2 q (h2 q hq))

end

end AronowAudit.P029.Wave1.PackageWeightedFit
