import SAP.P015b.WH.W3.Leaves
import SAP.P015b.WH.W3.P.T10_L1
import SAP.P015b.WH.W3.P.T10_L2
import SAP.P015b.WH.W3.P.T10_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P015b.WH.W3.T10_whole : SAP.P015b.T10WholeStatement_W3 :=
  SAP.P015b.WH.W3.T10_assembly SAP.P015b.WH.W3.T10_L1_proof SAP.P015b.WH.W3.T10_L2_proof SAP.P015b.WH.W3.T10_L3_proof
