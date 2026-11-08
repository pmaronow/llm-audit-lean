import SAP.P020.WH.W1.Leaves
import SAP.P020.WH.W1.P.T17_L1
import SAP.P020.WH.W1.P.T17_L2
import SAP.P020.WH.W1.P.T17_L3
import SAP.P020.WH.W1.P.T17_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P020.WH.W1.T17_whole : SAP.P020.T17WholeStatement :=
  SAP.P020.WH.W1.T17_assembly SAP.P020.WH.W1.T17_L1_proof SAP.P020.WH.W1.T17_L2_proof SAP.P020.WH.W1.T17_L3_proof SAP.P020.WH.W1.T17_L4_proof
