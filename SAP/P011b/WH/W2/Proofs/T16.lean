import SAP.P011b.WH.W2.Leaves
import SAP.P011b.WH.W2.P.T16_L1
import SAP.P011b.WH.W2.P.T16_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P011b.WH.W2.T16_whole : SAP.P011b.T16WholeStatement_W2 :=
  SAP.P011b.WH.W2.T16_assembly SAP.P011b.WH.W2.T16_L1_proof SAP.P011b.WH.W2.T16_L2_proof
