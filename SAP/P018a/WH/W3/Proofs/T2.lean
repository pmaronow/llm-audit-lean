import SAP.P018a.WH.W3.Leaves
import SAP.P018a.WH.W3.P.T2_L1
import SAP.P018a.WH.W3.P.T2_L2
import SAP.P018a.WH.W3.P.T2_L3
import SAP.P018a.WH.W3.P.T2_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P018a.WH.W3.T2_whole : SAP.P018a.T2WholeStatement_W3 :=
  SAP.P018a.WH.W3.T2_assembly SAP.P018a.WH.W3.T2_L1_proof SAP.P018a.WH.W3.T2_L2_proof SAP.P018a.WH.W3.T2_L3_proof SAP.P018a.WH.W3.T2_L4_proof
