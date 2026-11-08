import SAP.P061a.WH.W1.Leaves
import SAP.P061a.WH.W1.P.T4_L1
import SAP.P061a.WH.W1.P.T4_L2
import SAP.P061a.WH.W1.P.T4_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P061a.WH.W1.T4_whole : SAP.P061a.T4WholeStatement :=
  SAP.P061a.WH.W1.T4_assembly SAP.P061a.WH.W1.T4_L1_proof SAP.P061a.WH.W1.T4_L2_proof SAP.P061a.WH.W1.T4_L3_proof
