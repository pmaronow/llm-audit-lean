import AronowAudit.P027.Wave1.AePartitionBlueprint

namespace AronowAudit.P027.Wave1.AePartition

set_option autoImplicit false
noncomputable section
open AronowAudit.P027
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- A zero sum of nonnegative disagreement contributions vanishes termwise. -/
theorem n1_proof : N1 := by
  intro G Ω _ _ n D hco ω hω g i j
  have hnonneg : ∀ ξ ∈ (Finset.univ : Finset Ω),
      0 ≤ D.weight ξ *
        (if D.selected ξ ⟨g,i⟩ = D.selected ξ ⟨g,j⟩ then (0 : ℝ) else 1) := by
    intro ξ _
    split_ifs
    · simp only [mul_zero, le_refl]
    · simpa only [mul_one] using D.nonneg ξ
  have hsum :
      (∑ ξ : Ω, D.weight ξ *
        (if D.selected ξ ⟨g,i⟩ = D.selected ξ ⟨g,j⟩ then (0 : ℝ) else 1)) = 0 :=
    hco g i j
  have hterm : D.weight ω *
      (if D.selected ω ⟨g,i⟩ = D.selected ω ⟨g,j⟩ then (0 : ℝ) else 1) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum ω (Finset.mem_univ ω)
  by_contra hne
  have hz : D.weight ω = 0 := by
    simpa only [ite_eq_right hne, mul_one] using hterm
  exact (ne_of_gt hω) hz

end
end AronowAudit.P027.Wave1.AePartition
