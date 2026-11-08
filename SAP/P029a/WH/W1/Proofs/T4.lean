import SAP.P029a.WH.W1.Leaves
import SAP.P029a.WH.W1.P.T4_L1
import SAP.P029a.WH.W1.P.T4_L2
import SAP.P029a.WH.W1.P.T4_L3
import SAP.P029a.WH.W1.P.T4_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P029a.WH.W1.T4_whole : SAP.P029a.T4WholeStatement :=
  SAP.P029a.WH.W1.T4_assembly SAP.P029a.WH.W1.T4_L1_proof SAP.P029a.WH.W1.T4_L2_proof SAP.P029a.WH.W1.T4_L3_proof SAP.P029a.WH.W1.T4_L4_proof
