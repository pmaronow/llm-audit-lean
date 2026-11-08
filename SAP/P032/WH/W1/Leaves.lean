import SAP.P032.Defs.WholeW1
import AronowAudit.P032.P032_Dyadic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032.WH.W1

open scoped BigOperators

/-- Assemble all four clauses of P032-T9 from the existing finite matrix identities.
The SAP formulas are definitionally the donor formulas. The coefficient donor has
no denominator premises; its concrete specialization certifies the nonzero gap.
No new mathematical leaves are required. -/
theorem T9_assembly : T9WholeStatement := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P J _ _ m hm s a ha U hU b
    exact AronowAudit.P032.rubin_pooling_gap hm s a ha U hU b
  · exact AronowAudit.P032.dcr_weights_sum
  · intro P _ k m hm U hU b
    exact AronowAudit.P032.rubin_unadjusted_commutes hm
      (AronowAudit.P032.dcrWeight k) (AronowAudit.P032.dcr_weights_sum k) U hU b
  · exact AronowAudit.P032.asylike_coefficient_gap
  · norm_num [decompositionWeight, undoFactors, Fintype.sum_sum_type, Fin.sum_univ_succ]
  · norm_num [decompositionWeight, undoFactors, Fintype.sum_sum_type, Fin.sum_univ_succ]

end SAP.P032.WH.W1
