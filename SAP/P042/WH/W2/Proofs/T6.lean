import SAP.P042.WH.W2.Leaves
import SAP.P042.WH.W2.P.T6_L1
import SAP.P042.WH.W2.P.T6_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P042.WH.W2.T6_whole : SAP.P042.T6WholeStatement_W2 :=
  SAP.P042.WH.W2.T6_assembly SAP.P042.WH.W2.T6_L1_proof SAP.P042.WH.W2.T6_L2_proof
