import SAP.P002b.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory

/-- Corrected Algorithms 1/3 and 2/4 have completed runs returning the empirical
confidence set; when no curves cross, any quantile-attaining comparison returns it.
No assertion about termination under every prescribed choice policy is included. -/
def T28Statement : Prop :=
  ∀ (M : ℕ) (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ),
    0 < M → (0 < α ∧ α < 1) → DataGeneratedCoefficients Qf Qg →
    ARRegular Qf → (∀ m, ARRegular (Qg m)) →
    let f := arFunction Qf
    let g := fun m => arFunction (Qg m)
    (∃ J, IntersectionList g J) ∧
    (∀ J, IntersectionList g J → ∃ pieces, Algorithm1Run g α J pieces) ∧
    (∀ J pieces, Algorithm1Run g α J pieces →
      returnedSet f g pieces = mcSet f g α) ∧
    (∀ J, IntersectionList g J → J ≠ [] →
      ∃ pieces, Algorithm2Run g α J pieces) ∧
    (∀ J pieces, Algorithm2Run g α J pieces →
      returnedSet f g pieces = mcSet f g α) ∧
    (∀ J, IntersectionList g J → J = [] →
      (∀ β, (mcIndices g α β).Nonempty) ∧
      ∀ β m, m ∈ mcIndices g α β → {x | f x ≤ g m x} = mcSet f g α)

end
end SAP.P002b
