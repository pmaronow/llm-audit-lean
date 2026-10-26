import AronowAudit.P027.Wave1.AePartitionBlueprint

namespace AronowAudit.P027.Wave1.AePartition

set_option autoImplicit false
noncomputable section
open AronowAudit.P027
attribute [local instance] Classical.propDecidable

/-- Compare the original design with the lift of its representative design,
then apply the existing exact aggregation identities. -/
theorem n3_proof : N3 := by
  intro G Ω _ _ n hn D hD hs hpi hjoint y ω hω
  have hpos : Positive (repDesign n hn D) := by
    intro g
    rw [← hpi g ⟨0, hn g⟩]
    exact hD ⟨g,⟨0, hn g⟩⟩
  have hpiLift (k : Σ g, Fin (n g)) :
      pi D k = pi (liftDesign (repDesign n hn D) n) k := by
    rcases k with ⟨g,i⟩
    rw [lift_pi]
    exact hpi g i
  have hjointLift (k l : Σ g, Fin (n g)) :
      joint D k l = joint (liftDesign (repDesign n hn D) n) k l := by
    rcases k with ⟨g,i⟩
    rcases l with ⟨h,j⟩
    rw [lift_joint]
    exact hjoint g h i j
  have hindLift (k : Σ g, Fin (n g)) :
      indicator D ω k = indicator (liftDesign (repDesign n hn D) n) ω k := by
    rcases k with ⟨g,i⟩
    change (if D.selected ω ⟨g,i⟩ then (1 : ℝ) else 0) =
      (if D.selected ω ⟨g,⟨0, hn g⟩⟩ then (1 : ℝ) else 0)
    rw [hs ω hω g i]
  have hcovLift (k l : Σ g, Fin (n g)) :
      inclusionCov D k l = inclusionCov (liftDesign (repDesign n hn D) n) k l := by
    simp only [inclusionCov, hjointLift k l, hpiLift k, hpiLift l]
  constructor
  · calc
      htTotal D y ω = htTotal (liftDesign (repDesign n hn D) n) y ω := by
        unfold htTotal
        apply Finset.sum_congr rfl
        intro k _
        rw [hindLift k, hpiLift k]
      _ = htTotal (repDesign n hn D) (groupTotal n y) ω :=
        aggregation_total_preserved (repDesign n hn D) hpos n y ω
  · calc
      htVarianceEstimator D y ω =
          htVarianceEstimator (liftDesign (repDesign n hn D) n) y ω := by
        unfold htVarianceEstimator
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        simp only [hjointLift k l, hindLift k, hindLift l, hcovLift k l,
          hpiLift k, hpiLift l]
      _ = htVarianceEstimator (repDesign n hn D) (groupTotal n y) ω :=
        aggregation_ht_estimator_preserved (repDesign n hn D) hpos n y ω

end
end AronowAudit.P027.Wave1.AePartition
