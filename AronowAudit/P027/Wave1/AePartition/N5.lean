import AronowAudit.P027.Wave1.AePartitionBlueprint

namespace AronowAudit.P027.Wave1.AePartition

set_option autoImplicit false
noncomputable section
open AronowAudit.P027
attribute [local instance] Classical.propDecidable

/-- `biasA` depends only on the joint probabilities; transfer to a lift before
using the positive-design aggregation theorem. -/
theorem n5_proof : N5 := by
  intro G Ω _ _ n hn D hD hpi hjoint y
  have hpos : Positive (repDesign n hn D) := by
    intro g
    rw [← hpi g ⟨0, hn g⟩]
    exact hD ⟨g,⟨0, hn g⟩⟩
  have hjointLift (k l : Σ g, Fin (n g)) :
      joint D k l = joint (liftDesign (repDesign n hn D) n) k l := by
    rcases k with ⟨g,i⟩
    rcases l with ⟨h,j⟩
    rw [lift_joint]
    exact hjoint g h i j
  calc
    biasA D y = biasA (liftDesign (repDesign n hn D) n) y := by
      unfold biasA
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [hjointLift k l]
    _ = biasA (repDesign n hn D) (groupTotal n y) :=
      aggregation_A_preserved (repDesign n hn D) hpos n y

end
end AronowAudit.P027.Wave1.AePartition
