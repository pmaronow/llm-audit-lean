import SAP.P026a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P026a.WH.W2.P.T7_L3

open Finset
open scoped BigOperators
noncomputable section

open SAP.P026a.WH.W2

theorem ipw_weight_certificate (w : W2Allocation) (i : Fin 16) :
    0 < w2IPWWeight w i ∧
      w2IPWWeight w i =
        1 / inclusion paperTableUnitDesign (paperTableUnitDesign.treatment w i) i := by
  have hm := unit_marginal (paperTableUnitDesign.treatment w i) i
  constructor
  · unfold w2IPWWeight
    split_ifs <;> norm_num
  · rw [hm]
    fin_cases i <;>
      (cases ht : paperTableUnitDesign.treatment w _ <;>
        norm_num [w2IPWWeight, paperTableCluster,
          AronowAudit.P026.tableMarginal, ht] <;>
        simpa using ht)

theorem _root_.SAP.P026a.WH.W2.T7_L3_proof : SAP.P026a.WH.W2.T7_L3 := by
  intro w
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact ipw_weight_certificate w i
  · fin_cases w <;> decide +kernel
  · fin_cases w <;> decide +kernel
  · unfold w2ValidFit
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact le_of_lt (ipw_weight_certificate w i).1
    · fin_cases w <;> decide +kernel
    · fin_cases w <;> decide +kernel

end
end SAP.P026a.WH.W2.P.T7_L3
