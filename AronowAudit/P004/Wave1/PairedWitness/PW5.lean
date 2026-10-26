import AronowAudit.P004.Wave1.PairedWitness.PW4

namespace AronowAudit.P004.Wave1.PairedWitness

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators Classical

/-- The table at i reads only coordinates in the same block of length two. -/
theorem pairedTable_congr_block {N : ℕ} (i : Fin N) (z z' : Assignment N)
    (hz : ∀ k : Fin N, k.val / 2 = i.val / 2 → z k = z' k) :
    pairedTable N i z = pairedTable N i z' := by
  unfold pairedTable
  by_cases hE : Even N
  · rw [if_pos hE, if_pos hE, hz i rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k ≠ i ∧ k.val / 2 = i.val / 2
    · rw [if_pos hk, if_pos hk, hz k hk.2]
    · rw [if_neg hk, if_neg hk]
  · rw [if_neg hE, if_neg hE]

theorem pw5_proof : PW5 := by
  intro N j k z b hfar
  have hblock : k.val / 2 ≠ j.val / 2 := by
    intro h
    have hclose := pair_block_close j k h.symm
    linarith
  apply pairedTable_congr_block
  intro l hl
  have hlk : l ≠ k := by
    intro h
    subst l
    exact hblock hl
  exact Function.update_of_ne hlk b z

end
end AronowAudit.P004.Wave1.PairedWitness
