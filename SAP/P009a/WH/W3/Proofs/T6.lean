import SAP.P009a.WH.W3.Leaves
import SAP.P009a.WH.W3.P.T6_L1
import SAP.P009a.WH.W3.P.T6_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P009a.WH.W3.T6_whole : SAP.P009a.T6WholeStatement :=
  SAP.P009a.WH.W3.T6_assembly SAP.P009a.WH.W3.T6_L1_proof SAP.P009a.WH.W3.T6_L2_proof
