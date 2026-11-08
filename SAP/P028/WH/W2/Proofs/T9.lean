import SAP.P028.WH.W2.Leaves
import SAP.P028.WH.W2.P.T9_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P028.WH.W2.T9_whole : SAP.P028.T9WholeStatement :=
  SAP.P028.WH.W2.T9_assembly SAP.P028.WH.W2.T9_L1_proof
