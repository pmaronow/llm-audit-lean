import SAP.P008b.WH.W3.Leaves
import SAP.P008b.WH.W3.P.T16_L1
import SAP.P008b.WH.W3.P.T16_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P008b.WH.W3.T16_whole : SAP.P008b.T16WholeStatement_W3 :=
  SAP.P008b.WH.W3.T16_assembly SAP.P008b.WH.W3.T16_L1_proof SAP.P008b.WH.W3.T16_L2_proof
