import SAP.P009a.WH.W1.Leaves
import SAP.P009a.WH.W1.P.T16_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P009a.WH.W1.T16_whole : SAP.P009a.T16WholeStatement :=
  SAP.P009a.WH.W1.T16_assembly SAP.P009a.WH.W1.T16_L1_proof
