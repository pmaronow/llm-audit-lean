import AronowAudit.P004.Wave1.FiniteConditioningBlueprint

namespace AronowAudit.P004.Wave1.FiniteConditioning

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Conditioning depends only on the retained coordinates, even without overlap. -/
theorem fc1_proof : FC1 := by
  classical
  intro N p J U z z' hzz'
  have hden : (∏ j ∈ J, coin (p j) (z j)) =
      ∏ j ∈ J, coin (p j) (z' j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hzz' j hj]
  have hnum :
      (fun w : Assignment N => if ∀ j ∈ J, w j = z j then U w else 0) =
      (fun w : Assignment N => if ∀ j ∈ J, w j = z' j then U w else 0) := by
    funext w
    have he : (∀ j ∈ J, w j = z j) ↔ (∀ j ∈ J, w j = z' j) := by
      constructor
      · intro hw j hj
        exact (hw j hj).trans (hzz' j hj)
      · intro hw j hj
        exact (hw j hj).trans (hzz' j hj).symm
    exact if_congr he rfl rfl
  unfold conditionOn
  rw [hnum, hden]

end
end AronowAudit.P004.Wave1.FiniteConditioning
