import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Hausdorff

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- A real interior point exists even for infinite endpoints. A finite open
interval joining it to the desired endpoint suffices for the closure argument. -/
theorem n4_proof : N4 := by
  intro M g α m l u hg hcritical hlu hvalid β hβ
  let E : Set ℝ := {x | Real.sqrt (g m x) = mcCritical g α x}
  have hE : IsClosed E :=
    isClosed_eq (Real.continuous_sqrt.comp (hg m)) hcritical
  have hIE : openInterval l u ⊆ E := by
    intro x hx
    have hm := hvalid x hx
    exact (Finset.mem_filter.mp hm).2
  obtain ⟨c, hlc, hcu⟩ := EReal.exists_between_coe_real hlu
  have hc : c ∈ openInterval l u := ⟨hlc, hcu⟩
  have hβE : β ∈ E := by
    rcases lt_trichotomy β c with hβc | hβc | hcβ
    · have hsub : Set.Ioo β c ⊆ E := by
        intro t ht
        apply hIE
        exact ⟨lt_of_le_of_lt hβ.1 (EReal.coe_lt_coe_iff.mpr ht.1),
          lt_trans (EReal.coe_lt_coe_iff.mpr ht.2) hcu⟩
      apply closure_minimal hsub hE
      rw [closure_Ioo hβc.ne]
      exact ⟨le_rfl, hβc.le⟩
    · exact hβc.symm ▸ hIE hc
    · have hsub : Set.Ioo c β ⊆ E := by
        intro t ht
        apply hIE
        exact ⟨lt_trans hlc (EReal.coe_lt_coe_iff.mpr ht.1),
          lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr ht.2) hβ.2⟩
      apply closure_minimal hsub hE
      rw [closure_Ioo hcβ.ne]
      exact ⟨hcβ.le, le_rfl⟩
  simp only [mcIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hβE

end
end AronowAudit.P002.Wave1.AlgorithmSupport
