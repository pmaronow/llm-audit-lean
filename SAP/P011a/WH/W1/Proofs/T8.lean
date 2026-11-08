import SAP.P011a.WH.W1.Leaves
import SAP.P011a.WH.W1.P.T6_L1
import SAP.P011a.WH.W1.P.T7_L1
import SAP.P011a.WH.W1.P.T7_L3
import SAP.P011a.WH.W1.P.T7_L4
import SAP.P011a.WH.W1.P.T8_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P011a.WH.W1.T8_whole : SAP.P011a.T8WholeStatement :=
  SAP.P011a.WH.W1.T8_assembly SAP.P011a.WH.W1.T6_L1_proof SAP.P011a.WH.W1.T7_L1_proof SAP.P011a.WH.W1.T7_L3_proof SAP.P011a.WH.W1.T7_L4_proof SAP.P011a.WH.W1.T8_L1_proof
