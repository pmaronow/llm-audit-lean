import AronowAudit.P005.Wave1.ExactDecompositionBlueprint

set_option autoImplicit false

namespace AronowAudit.P005.Wave1.ExactDecomposition

open AronowAudit.P005 Finset
open scoped BigOperators

noncomputable section

theorem n6_proof : N6 := by
  classical
  intro n d m P hn hm hmn hP hreg S hS
  have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
  have hsN : S.Nonempty := Finset.card_pos.mp (by rw [hs]; exact hm)
  have hc : (control S).card = n - m := by
    rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp only [Finset.card_univ, Fintype.card_fin, hs]
  have hcN : (control S).Nonempty :=
    Finset.card_pos.mp (by rw [hc]; exact Nat.sub_pos_of_lt hmn)
  exact ⟨arm_slope_decomposition P hP S hsN P.yT (hreg S hS).1,
    arm_slope_decomposition P hP (control S) hcN P.yC (hreg S hS).2⟩

end

end AronowAudit.P005.Wave1.ExactDecomposition
