import SAP.P004a.WH.W2.Leaves
import SAP.P004a.WH.W2.P.T14_L1
import SAP.P004a.WH.W2.P.T14_L2
import SAP.P004a.WH.W2.P.T14_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004a.WH.W2.T14_whole : SAP.P004a.T14WholeStatement :=
  SAP.P004a.WH.W2.T14_assembly SAP.P004a.WH.W2.T14_L1_proof SAP.P004a.WH.W2.T14_L2_proof SAP.P004a.WH.W2.T14_L3_proof
