import SAP.P009a.WH.W3.Leaves
import SAP.P009a.WH.W3.P.T7_L1
import SAP.P009a.WH.W3.P.T7_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P009a.WH.W3.T7_whole : SAP.P009a.T7WholeStatement :=
  SAP.P009a.WH.W3.T7_assembly SAP.P009a.WH.W3.T7_L1_proof SAP.P009a.WH.W3.T7_L2_proof
