import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint
import Mathlib.Analysis.Real.Sqrt

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem n5_proof : N5 := by
  intro M f g α p _hf hg hvalid
  have hη (β : ℝ) (hβ : β ∈ closedInterval p.left p.right) :
      Real.sqrt (g p.index β) = mcCritical g α β := by
    have hm := hvalid β hβ
    simpa only [mcIndices, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  constructor
  · intro β hβ
    calc
      g p.index β = Real.sqrt (g p.index β) ^ 2 :=
        (Real.sq_sqrt (hg p.index β)).symm
      _ = (mcCritical g α β) ^ 2 := congrArg (fun x : ℝ => x ^ 2) (hη β hβ)
  · apply Set.ext
    intro β
    change (β ∈ closedInterval p.left p.right ∧ f β ≤ g p.index β) ↔
      (Real.sqrt (f β) ≤ mcCritical g α β ∧ β ∈ closedInterval p.left p.right)
    constructor
    · rintro ⟨hβ, hfg⟩
      refine ⟨?_, hβ⟩
      rw [← hη β hβ]
      exact (Real.sqrt_le_sqrt_iff (hg p.index β)).mpr hfg
    · rintro ⟨hfq, hβ⟩
      refine ⟨hβ, ?_⟩
      rw [← hη β hβ] at hfq
      exact (Real.sqrt_le_sqrt_iff (hg p.index β)).mp hfq

end
end AronowAudit.P002.Wave1.AlgorithmSupport
