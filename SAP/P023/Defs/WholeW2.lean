import Mathlib
import SAP.P023.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P023

open scoped BigOperators

/-- P023-T11; Proposition 1, p. 6 (PDF p. 6); Conditions 1–3, p. 5
(PDF p. 5); Appendix A, p. 9 (PDF p. 9).
For finite two-party election data with margins in [-1,1], binary win indicators
agreeing with the signs of nonzero margins, bandwidth 0 < k < 1, and the two
strictly interior observations required by Condition 1, both party counts in
U_b = (-k,k] are positive. Every least-squares solution of the all-election
regression with an intercept, the win indicator, and the printed width-2k bin
indicators of Condition 2 has win coefficient equal to the degree-zero,
rectangular-kernel RD difference in means of Condition 3. Ties may have either
binary indicator and nuisance bins may be empty. All sums here are finite.
Restriction: States the estimator-equality result under Conditions 1–3; omits the printed remark that Condition 1 is necessary for an RD estimate to exist. -/
def T11WholeStatement_W2 : Prop :=
  ∀ {ι : Type} [Fintype ι] (k : ℝ) (_hk : 0 < k ∧ k < 1)
    (x d y : ι → ℝ) (_hdata : TwoParty x d) (_h1 : Condition1 k x),
    (0 < ∑ i ∈ close k x, d i) ∧
    (0 < ∑ i ∈ close k x, (1 - d i)) ∧
    ∀ c : Fin (binCount k + 2) → ℝ,
      IsOLS (coarsenedDesign k x d) y c →
      c ⟨1, by omega⟩ = rd k x d y

end SAP.P023
