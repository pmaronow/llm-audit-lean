import SAP.P026a.WH.W1.Leaves
import SAP.P026a.WH.W1.P.T6_L1
import SAP.P026a.WH.W1.P.T6_L2
import SAP.P026a.WH.W1.P.T6_L3
import SAP.P026a.WH.W1.P.T6_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P026a.WH.W1.T6_whole : SAP.P026a.T6WholeStatement :=
  SAP.P026a.WH.W1.T6_assembly SAP.P026a.WH.W1.T6_L1_proof SAP.P026a.WH.W1.T6_L2_proof SAP.P026a.WH.W1.T6_L3_proof SAP.P026a.WH.W1.T6_L4_proof
