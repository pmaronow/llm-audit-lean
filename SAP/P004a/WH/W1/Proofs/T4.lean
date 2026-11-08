import SAP.P004a.WH.W1.Leaves
import SAP.P004a.WH.W1.P.T3_L3
import SAP.P004a.WH.W1.P.T4_L1
import SAP.P004a.WH.W1.P.T4_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004a.WH.W1.T4_whole : SAP.P004a.T4WholeStatement :=
  SAP.P004a.WH.W1.T4_assembly SAP.P004a.WH.W1.T3_L3_proof SAP.P004a.WH.W1.T4_L1_proof SAP.P004a.WH.W1.T4_L2_proof
