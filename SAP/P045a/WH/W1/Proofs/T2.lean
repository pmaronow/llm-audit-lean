import SAP.P045a.WH.W1.Leaves
import SAP.P045a.WH.W1.P.T2_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P045a.WH.W1.T2_whole : SAP.P045a.T2WholeStatement :=
  SAP.P045a.WH.W1.T2_assembly SAP.P045a.WH.W1.T2_L1_proof
