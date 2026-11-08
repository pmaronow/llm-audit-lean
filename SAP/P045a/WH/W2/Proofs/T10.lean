import SAP.P045a.WH.W2.Leaves
import SAP.P045a.WH.W2.P.T10_L1
import SAP.P045a.WH.W2.P.T10_L2
import SAP.P045a.WH.W2.P.T10_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P045a.WH.W2.T10_whole : SAP.P045a.T10WholeStatement :=
  SAP.P045a.WH.W2.T10_assembly SAP.P045a.WH.W2.T10_L1_proof SAP.P045a.WH.W2.T10_L2_proof SAP.P045a.WH.W2.T10_L3_proof
