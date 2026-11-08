import SAP.P003b.WH.W1.Leaves
import SAP.P003b.WH.W1.P.T18_L1
import SAP.P003b.WH.W1.P.T18_L2
import SAP.P003b.WH.W1.P.T18_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003b.WH.W1.T18_whole : SAP.P003b.T18WholeStatement :=
  SAP.P003b.WH.W1.T18_assembly SAP.P003b.WH.W1.T18_L1_proof SAP.P003b.WH.W1.T18_L2_proof SAP.P003b.WH.W1.T18_L3_proof
