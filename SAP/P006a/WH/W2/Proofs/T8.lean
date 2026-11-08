import SAP.P006a.WH.W2.Leaves
import SAP.P006a.WH.W2.P.T8_L1
import SAP.P006a.WH.W2.P.T8_L2
import SAP.P006a.WH.W2.P.T8_L3
import SAP.P006a.WH.W2.P.T8_L4
import SAP.P006a.WH.W2.P.T8_L5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P006a.WH.W2.T8_whole : SAP.P006a.T8WholeStatement_W2 :=
  SAP.P006a.WH.W2.T8_assembly SAP.P006a.WH.W2.T8_L1_proof SAP.P006a.WH.W2.T8_L2_proof SAP.P006a.WH.W2.T8_L3_proof SAP.P006a.WH.W2.T8_L4_proof SAP.P006a.WH.W2.T8_L5_proof
