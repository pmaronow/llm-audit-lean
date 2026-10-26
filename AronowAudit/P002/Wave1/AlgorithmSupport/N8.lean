import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Sort

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- A finite union of the distinct-pair intersection sets can be sorted into the
complete intersection list. Identical curves contribute the empty set. -/
theorem n8_proof : N8 := by
  classical
  intro M g hreg
  let meet : Fin M → Fin M → Set ℝ :=
    fun s t => {β | g s ≠ g t ∧ g s β = g t β}
  have hmeet : ∀ s t, (meet s t).Finite := by
    intro s t
    by_cases hst : g s = g t
    · simpa [meet, hst] using (Set.finite_empty : (∅ : Set ℝ).Finite)
    · exact (hreg.2.2 s t hst).subset (fun β hβ => hβ.2)
  have hunion : (⋃ s : Fin M, ⋃ t : Fin M, meet s t).Finite :=
    Set.finite_iUnion fun s => Set.finite_iUnion fun t => hmeet s t
  have hcross : {β : ℝ | crossing g β}.Finite := by
    apply hunion.subset
    intro β hβ
    rcases hβ with ⟨s, t, hst, hstβ⟩
    exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨t, ⟨hst, hstβ⟩⟩⟩
  let S : Finset ℝ := hcross.toFinset
  refine ⟨S.sort (· ≤ ·), ?_⟩
  constructor
  · exact (Finset.sortedLT_sort S).pairwise
  · intro β
    change β ∈ S.sort (· ≤ ·) ↔ crossing g β
    rw [Finset.mem_sort]
    exact hcross.mem_toFinset

end
end AronowAudit.P002.Wave1.AlgorithmSupport
