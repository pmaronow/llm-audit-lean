import AronowAudit.P005.Wave1.ExactDecompositionBlueprint

set_option autoImplicit false

namespace AronowAudit.P005.Wave1.ExactDecomposition

open AronowAudit.P005 Finset
open scoped BigOperators

noncomputable section

/-- Complementation transports the uniform design, including its endpoints. -/
theorem n1_proof : N1 := by
  classical
  intro n m hmn F
  have hcard (S : Finset (Fin n)) : (control S).card = n - S.card := by
    rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp only [Finset.card_univ, Fintype.card_fin]
  have hinvol (S : Finset (Fin n)) : control (control S) = S := by
    exact Finset.sdiff_sdiff_eq_self (Finset.subset_univ S)
  have hforward : ∀ S ∈ design n m, control S ∈ design n (n - m) := by
    intro S hS
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [hcard, (Finset.mem_powersetCard.mp hS).2]
  have hbackward : ∀ S ∈ design n (n - m), control S ∈ design n m := by
    intro S hS
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [hcard, (Finset.mem_powersetCard.mp hS).2, Nat.sub_sub_self hmn]
  have hsum : (∑ S ∈ design n m, F (control S)) =
      ∑ S ∈ design n (n - m), F S := by
    exact Finset.sum_nbij' control control hforward hbackward
      (fun S _ => hinvol S) (fun S _ => hinvol S) (fun _ _ => rfl)
  have hden : (design n m).card = (design n (n - m)).card := by
    simp only [design, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact (Nat.choose_symm hmn).symm
  unfold expectation
  rw [hsum, hden]

end

end AronowAudit.P005.Wave1.ExactDecomposition
