import SAP.P009a.WH.W2.Leaves
import SAP.P009a.WH.W2.P.T4_L1
import SAP.P009a.WH.W2.P.T4_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P009a.WH.W2.T4_whole : SAP.P009a.T4WholeStatement :=
  SAP.P009a.WH.W2.T4_assembly SAP.P009a.WH.W2.T4_L1_proof SAP.P009a.WH.W2.T4_L2_proof
