import Mathlib
import SAP.P007.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P007

/-- P007-T10; corrected Figure 5 and its discussion, Supplement pp. 2-3.
The printed claim is false: its unqualified assertion that the bounds coincide
only when n=1 fails at the allowed endpoint q=0. For n=2 and k=1, the normalized
independent-cell law with observation probability zero satisfies Assumptions 1
and 2. Every entry is missing almost surely, every row has survival probability
zero and expected deletion indicator one, and the expected deleted fraction and
all-deletion probability are one. Both b_1 and the all-deletion lower bound are
one, although n is not one. Thus full-domain coincidence does not imply n=1. -/
def T10WholeStatement : Prop :=
  (∃ L : Law (Array 2 1),
    L.weight = equalWeights 2 1 0 ∧
    rowIndependent L ∧ observationBound L 0 ∧
    (∀ i : Fin 2,
      probability L (fun x => x i 0 = true) = 1 ∧
      survival L i 1 = 0 ∧
      expectation L (fun x => deletedIndicator x i) = 1) ∧
    expectation L deletedFraction = 1 ∧ allDeleted L = 1) ∧
  fractionBound 0 1 = 1 ∧ lowerBound 2 0 1 = 1 ∧
  lowerBound 2 0 1 = fractionBound 0 1 ∧ (2 : ℕ) ≠ 1 ∧
  ¬ (∀ (n k : ℕ), 0 < n → 0 < k → ∀ q : ℝ, 0 ≤ q → q < 1 →
    lowerBound n q k = fractionBound q k → n = 1)

end SAP.P007
