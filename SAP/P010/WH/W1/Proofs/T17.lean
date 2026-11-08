import SAP.P010.WH.W1.Leaves
import SAP.P010.WH.W1.P.T17_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P010.WH.W1.T17_whole : SAP.P010.T17WholeStatement :=
  SAP.P010.WH.W1.T17_assembly SAP.P010.WH.W1.T17_L1_proof
