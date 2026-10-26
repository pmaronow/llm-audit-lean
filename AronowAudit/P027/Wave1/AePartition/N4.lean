import AronowAudit.P027.Wave1.AePartitionBlueprint

namespace AronowAudit.P027.Wave1.AePartition

set_option autoImplicit false
noncomputable section
open AronowAudit.P027
attribute [local instance] Classical.propDecidable

/-- First identify the weighted means, then compare the squared deviations. -/
theorem n4_proof : N4 := by
  intro U U' Ω _ _ _ D D' hw f f' hs
  have he (a b : Ω → ℝ) (hab : ∀ ω, 0 < D.weight ω → a ω = b ω) :
      expect D a = expect D' b := by
    unfold expect
    apply Finset.sum_congr rfl
    intro ω _
    rw [← hw ω]
    by_cases hω : 0 < D.weight ω
    · rw [hab ω hω]
    · have hz : D.weight ω = 0 :=
        le_antisymm (le_of_not_gt hω) (D.nonneg ω)
      simp only [hz, zero_mul]
  have hm : expect D f = expect D' f' := he f f' hs
  refine ⟨hm, ?_⟩
  unfold variance
  apply he
  intro ω hω
  rw [hs ω hω, hm]

end
end AronowAudit.P027.Wave1.AePartition
