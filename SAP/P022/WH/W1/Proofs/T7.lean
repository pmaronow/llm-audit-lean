import SAP.P022.WH.W1.Leaves
import SAP.P022.WH.W1.P.T7_L1
import SAP.P022.WH.W1.P.T7_L2
import SAP.P022.WH.W1.P.T7_L3
import SAP.P022.WH.W1.P.T7_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P022.WH.W1.T7_whole : SAP.P022.T7WholeStatement :=
  SAP.P022.WH.W1.T7_assembly SAP.P022.WH.W1.T7_L1_proof SAP.P022.WH.W1.T7_L2_proof SAP.P022.WH.W1.T7_L3_proof SAP.P022.WH.W1.T7_L4_proof
