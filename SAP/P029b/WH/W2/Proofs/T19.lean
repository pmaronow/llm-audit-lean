import SAP.P029b.WH.W2.Leaves
import SAP.P029b.WH.W2.P.T19_L1
import SAP.P029b.WH.W2.P.T19_L2
import SAP.P029b.WH.W2.P.T19_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P029b.WH.W2.T19_whole : SAP.P029b.T19WholeStatement :=
  SAP.P029b.WH.W2.T19_assembly SAP.P029b.WH.W2.T19_L1_proof SAP.P029b.WH.W2.T19_L2_proof SAP.P029b.WH.W2.T19_L3_proof
