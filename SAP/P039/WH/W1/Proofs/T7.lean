import SAP.P039.WH.W1.Leaves
import SAP.P039.WH.W1.P.T7_L1
import SAP.P039.WH.W1.P.T7_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P039.WH.W1.T7_whole : SAP.P039.T7WholeStatement :=
  SAP.P039.WH.W1.T7_assembly SAP.P039.WH.W1.T7_L1_proof SAP.P039.WH.W1.T7_L2_proof
