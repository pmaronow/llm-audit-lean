import SAP.P028.WH.W1.Leaves
import SAP.P028.WH.W1.P.T10_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P028.WH.W1.T10_whole : SAP.P028.T10WholeStatement :=
  SAP.P028.WH.W1.T10_assembly SAP.P028.WH.W1.T10_L1_proof
