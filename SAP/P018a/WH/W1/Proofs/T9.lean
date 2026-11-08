import SAP.P018a.WH.W1.Leaves
import SAP.P018a.WH.W1.P.T9_L1
import SAP.P018a.WH.W1.P.T9_L2
import SAP.P018a.WH.W1.P.T9_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P018a.WH.W1.T9_whole : SAP.P018a.T9WholeStatement :=
  SAP.P018a.WH.W1.T9_assembly SAP.P018a.WH.W1.T9_L1_proof SAP.P018a.WH.W1.T9_L2_proof SAP.P018a.WH.W1.T9_L3_proof
