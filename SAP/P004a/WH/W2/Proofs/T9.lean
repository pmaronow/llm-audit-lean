import SAP.P004a.WH.W2.Leaves
import SAP.P004a.WH.W2.P.T9_L1
import SAP.P004a.WH.W2.P.T9_L2
import SAP.P004a.WH.W2.P.T9_L3
import SAP.P004a.WH.W2.P.T9_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004a.WH.W2.T9_whole : SAP.P004a.T9WholeStatement :=
  SAP.P004a.WH.W2.T9_assembly SAP.P004a.WH.W2.T9_L1_proof SAP.P004a.WH.W2.T9_L2_proof SAP.P004a.WH.W2.T9_L3_proof SAP.P004a.WH.W2.T9_L4_proof
