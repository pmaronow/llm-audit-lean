import SAP.P031.WH.W2.Luna.T5_L1
import SAP.P031.WH.W2.Sol.T5_L2
import SAP.P031.WH.W2.Sol.T5_L3
import SAP.P031.WH.W2.Luna.T5_L4
import SAP.P031.WH.W2.Luna.T5_L5
import SAP.P031.WH.W2.Luna.T5_L6
import SAP.P031.WH.W2.Luna.T5_L7

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Restricted cited-regime T5 candidate under the explicit D>0 premise. -/
theorem SAP.P031.WH.W2.T5_cited : SAP.P031.T5CitedRegimeStatement :=
  SAP.P031.WH.W2.T5_assembly
    SAP.P031.WH.W2.Luna.T5_L1_solution
    SAP.P031.WH.W2.Sol.T5_L2_solution
    SAP.P031.WH.W2.Sol.T5_L3_solution
    SAP.P031.WH.W2.Luna.T5_L4_solution
    SAP.P031.WH.W2.Luna.T5_L5_solution
    SAP.P031.WH.W2.Luna.T5_L6_solution
    SAP.P031.WH.W2.Luna.T5_L7_solution
