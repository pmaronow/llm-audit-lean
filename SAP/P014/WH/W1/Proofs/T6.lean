import SAP.P014.WH.W1.Leaves
import SAP.P014.WH.W1.P.T6_L1
import SAP.P014.WH.W1.P.T6_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P014.WH.W1.T6_whole : SAP.P014.T6WholeStatement :=
  SAP.P014.WH.W1.T6_assembly SAP.P014.WH.W1.T6_L1_proof SAP.P014.WH.W1.T6_L2_proof
