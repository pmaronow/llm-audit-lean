import SAP.P039.WH.W1.Leaves
import SAP.P039.WH.W1.P.T4_L1
import SAP.P039.WH.W1.P.T4_L2
import SAP.P039.WH.W1.P.T4_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P039.WH.W1.T4_whole : SAP.P039.T4WholeStatement :=
  SAP.P039.WH.W1.T4_assembly SAP.P039.WH.W1.T4_L1_proof SAP.P039.WH.W1.T4_L2_proof SAP.P039.WH.W1.T4_L3_proof
