import SAP.P002b.Defs
import SAP.P002b.Bridge.Part1
import AronowAudit.P002.P002_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b.Bridge
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory

/-- Reindex the two tail suprema through the field-preserving population
adapters. The probabilities and normal cutoffs agree by reduction, including
the value zero for an empty model supremum. -/
theorem adjustedTailSupremum_eq (n k : ℕ) (δ e A B r α κ : ℝ) :
    adjustedTailSupremum n k δ e A B r α κ =
      AronowAudit.P002.supAdjustedTail n k δ e A B r α κ := by
  unfold adjustedTailSupremum AronowAudit.P002.supAdjustedTail
  apply le_antisymm
  · refine iSup_le fun β => iSup_le fun P => ?_
    exact le_iSup_of_le β (le_iSup_of_le ⟨toCovPopulation P.val, P.property⟩ le_rfl)
  · refine iSup_le fun β => iSup_le fun P => ?_
    exact le_iSup_of_le β (le_iSup_of_le ⟨fromCovPopulation P.val, P.property⟩ le_rfl)

end
end SAP.P002b.Bridge
