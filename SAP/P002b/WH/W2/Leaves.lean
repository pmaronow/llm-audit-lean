import SAP.P002b.Defs.WholeW2
import SAP.P002b.Bridge
import AronowAudit.P002.Wave1.Gap.RepairT21
import AronowAudit.P002.Wave1.Lib.FinitePopulationCLT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b.WH.W2

open scoped ENNReal
open Filter

/-- The corrected claim needs no new mathematical leaf. Apply the proved
finite-population CLT to the proved adjusted-tail theorem, and transport the
nested suprema through the population adapter. The significance bound also
puts the outer limit in [0, 1]. The donor includes zero residual variance. -/
theorem T21_assembly : T21WholeStatement := by
  intro k δ e A B r α hk hδ he hA hB hr hα
  obtain ⟨u, hu, hbound⟩ :=
    AronowAudit.P002.Wave1.corrected_theorem7_limsup_of_finitePopulationCLT
      AronowAudit.P002.Wave1.finitePopulationCLT
      k δ e A B r α hk hδ he hA hB hr hα
  refine ⟨u, ?_, ?_, hbound⟩
  · exact hbound.trans (by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hα.2.le)
  · simpa only [← Bridge.adjustedTailSupremum_eq] using hu

end SAP.P002b.WH.W2
