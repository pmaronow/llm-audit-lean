import SAP.P003b.WH.W1.Leaves
import SAP.P003b.WH.W1.P.T7_L1
import SAP.P003b.WH.W1.P.T7_L2
import SAP.P003b.WH.W1.P.T7_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003b.WH.W1.T7_whole : SAP.P003b.T7WholeStatement :=
  SAP.P003b.WH.W1.T7_assembly SAP.P003b.WH.W1.T7_L1_proof SAP.P003b.WH.W1.T7_L2_proof SAP.P003b.WH.W1.T7_L3_proof
