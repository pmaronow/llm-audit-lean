import AronowAudit.P027.Wave1.AePartitionBlueprint

namespace AronowAudit.P027.Wave1.AePartition

set_option autoImplicit false
noncomputable section
open AronowAudit.P027
attribute [local instance] Classical.propDecidable

/-- Weighted indicators and indicator products ignore atoms of weight zero. -/
theorem n2_proof : N2 := by
  intro G Ω _ _ n hn D hs
  have hind : ∀ (ω : Ω), 0 < D.weight ω → ∀ (g : G) (i : Fin (n g)),
      indicator D ω ⟨g,i⟩ = indicator (repDesign n hn D) ω g := by
    intro ω hω g i
    change (if D.selected ω ⟨g,i⟩ then (1 : ℝ) else 0) =
      (if D.selected ω ⟨g,⟨0, hn g⟩⟩ then (1 : ℝ) else 0)
    rw [hs ω hω g i]
  constructor
  · intro g i
    unfold pi expect
    apply Finset.sum_congr rfl
    intro ω _
    change D.weight ω * indicator D ω ⟨g,i⟩ =
      D.weight ω * indicator (repDesign n hn D) ω g
    by_cases hω : 0 < D.weight ω
    · rw [hind ω hω g i]
    · have hz : D.weight ω = 0 :=
        le_antisymm (le_of_not_gt hω) (D.nonneg ω)
      simp only [hz, zero_mul]
  · intro g h i j
    unfold joint expect
    apply Finset.sum_congr rfl
    intro ω _
    change D.weight ω * (indicator D ω ⟨g,i⟩ * indicator D ω ⟨h,j⟩) =
      D.weight ω *
        (indicator (repDesign n hn D) ω g * indicator (repDesign n hn D) ω h)
    by_cases hω : 0 < D.weight ω
    · rw [hind ω hω g i, hind ω hω h j]
    · have hz : D.weight ω = 0 :=
        le_antisymm (le_of_not_gt hω) (D.nonneg ω)
      simp only [hz, zero_mul]

end
end AronowAudit.P027.Wave1.AePartition
