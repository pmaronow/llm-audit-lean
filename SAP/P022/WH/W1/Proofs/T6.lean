import SAP.P022.WH.W1.Leaves
import SAP.P022.WH.W1.P.T6_L1
import SAP.P022.WH.W1.P.T6_L2
import SAP.P022.WH.W1.P.T6_L3
import SAP.P022.WH.W1.P.T6_L4
import SAP.P022.WH.W1.P.T6_L5
import SAP.P022.WH.W1.P.T6_L6
import SAP.P022.WH.W1.P.T6_L7

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P022.WH.W1.T6_whole : SAP.P022.T6WholeStatement :=
  SAP.P022.WH.W1.T6_assembly SAP.P022.WH.W1.T6_L1_proof SAP.P022.WH.W1.T6_L2_proof SAP.P022.WH.W1.T6_L3_proof SAP.P022.WH.W1.T6_L4_proof SAP.P022.WH.W1.T6_L5_proof SAP.P022.WH.W1.T6_L6_proof SAP.P022.WH.W1.T6_L7_proof
