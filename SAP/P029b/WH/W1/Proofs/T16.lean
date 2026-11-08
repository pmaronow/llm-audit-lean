import SAP.P029b.WH.W1.Leaves
import SAP.P029b.WH.W1.P.T16_L1
import SAP.P029b.WH.W1.P.T16_L2
import SAP.P029b.WH.W1.P.T16_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P029b.WH.W1.T16_whole : SAP.P029b.T16WholeStatement :=
  SAP.P029b.WH.W1.T16_assembly SAP.P029b.WH.W1.T16_L1_proof SAP.P029b.WH.W1.T16_L2_proof SAP.P029b.WH.W1.T16_L3_proof
