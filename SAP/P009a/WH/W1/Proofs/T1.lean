import SAP.P009a.WH.W1.Leaves
import SAP.P009a.WH.W1.P.T1_L1
import SAP.P009a.WH.W1.P.T1_L2
import SAP.P009a.WH.W1.P.T1_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P009a.WH.W1.T1_whole : SAP.P009a.T1WholeStatement :=
  SAP.P009a.WH.W1.T1_assembly SAP.P009a.WH.W1.T1_L1_proof SAP.P009a.WH.W1.T1_L2_proof SAP.P009a.WH.W1.T1_L3_proof
