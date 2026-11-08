import SAP.P020.WH.W1.Leaves
import SAP.P020.WH.W1.P.T14_L1
import SAP.P020.WH.W1.P.T14_L2
import SAP.P020.WH.W1.P.T14_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P020.WH.W1.T14_whole : SAP.P020.T14WholeStatement :=
  SAP.P020.WH.W1.T14_assembly SAP.P020.WH.W1.T14_L1_proof SAP.P020.WH.W1.T14_L2_proof SAP.P020.WH.W1.T14_L3_proof
