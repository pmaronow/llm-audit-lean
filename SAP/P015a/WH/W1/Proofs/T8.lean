import SAP.P015a.WH.W1.Leaves
import SAP.P015a.WH.W1.P.T8_L1
import SAP.P015a.WH.W1.P.T8_L2
import SAP.P015a.WH.W1.P.T8_L3
import SAP.P015a.WH.W1.P.T8_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P015a.WH.W1.T8_whole : SAP.P015a.T8WholeStatement :=
  SAP.P015a.WH.W1.T8_assembly SAP.P015a.WH.W1.T8_L1_proof SAP.P015a.WH.W1.T8_L2_proof SAP.P015a.WH.W1.T8_L3_proof SAP.P015a.WH.W1.T8_L4_proof
