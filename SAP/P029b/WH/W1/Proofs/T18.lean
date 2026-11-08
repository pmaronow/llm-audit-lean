import SAP.P029b.WH.W1.Leaves
import SAP.P029b.WH.W1.P.T18_L1
import SAP.P029b.WH.W1.P.T18_L2
import SAP.P029b.WH.W1.P.T18_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P029b.WH.W1.T18_whole : SAP.P029b.T18WholeStatement :=
  SAP.P029b.WH.W1.T18_assembly SAP.P029b.WH.W1.T18_L1_proof SAP.P029b.WH.W1.T18_L2_proof SAP.P029b.WH.W1.T18_L3_proof
