import SAP.P031.WH.W1.Leaves
import SAP.P031.WH.W1.P.T6_L1
import SAP.P031.WH.W1.P.T6_L2
import SAP.P031.WH.W1.P.T6_L3
import SAP.P031.WH.W1.P.T6_L4
import SAP.P031.WH.W1.P.T6_L5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Assembly of the historical normality-only related result; uncredited to the
current cited-regime canonical claim. The legacy declaration name is retained. -/
theorem SAP.P031.WH.W1.T6_whole : SAP.P031.T6WholeStatement :=
  SAP.P031.WH.W1.T6_assembly SAP.P031.WH.W1.T6_L1_proof SAP.P031.WH.W1.T6_L2_proof SAP.P031.WH.W1.T6_L3_proof SAP.P031.WH.W1.T6_L4_proof SAP.P031.WH.W1.T6_L5_proof
