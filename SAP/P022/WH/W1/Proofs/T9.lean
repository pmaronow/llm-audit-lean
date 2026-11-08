import SAP.P022.WH.W1.Leaves
import SAP.P022.WH.W1.P.T9_L1
import SAP.P022.WH.W1.P.T9_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P022.WH.W1.T9_whole : SAP.P022.T9WholeStatement :=
  SAP.P022.WH.W1.T9_assembly SAP.P022.WH.W1.T9_L1_proof SAP.P022.WH.W1.T9_L2_proof
