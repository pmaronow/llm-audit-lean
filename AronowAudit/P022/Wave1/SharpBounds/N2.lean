import AronowAudit.P022.Wave1.SharpBoundsBlueprint
import Mathlib.Data.List.FinRange

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.SharpBounds
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem sortedValues_ofFn {N : ℕ} (y : Fin N → ℝ) :
    List.ofFn (sortedValues y) = sortedOutcomes y := by
  have hl : (sortedOutcomes y).length = N := by simp [sortedOutcomes]
  apply List.ext_getElem
  · simp [hl]
  · intro i hi hj
    simp only [List.getElem_ofFn, sortedValues, List.getD_eq_getElem (sortedOutcomes y) 0 hj]

theorem n2_proof : N2 := by
  intro N y
  have hp : List.Perm (List.ofFn (sortedValues y)) (List.ofFn y) := by
    rw [sortedValues_ofFn]
    exact List.mergeSort_perm _ _
  refine ⟨hp, ?_, ?_⟩
  · exact (Fin.revPerm.ofFn_comp_perm (sortedValues y)).trans hp
  · apply List.SortedLE.monotone
    rw [sortedValues_ofFn]
    exact List.sortedLE_mergeSort

end
end AronowAudit.P022.Wave1.SharpBounds
