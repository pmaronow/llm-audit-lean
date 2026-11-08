import SAP.P001e.WH.W4.Leaves
import SAP.P001e.WH.W4.P.T93_L1
import SAP.P001e.WH.W4.P.T93_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001e.WH.W4.T93_whole : SAP.P001e.T93WholeStatement_W4 :=
  SAP.P001e.WH.W4.T93_assembly SAP.P001e.WH.W4.T93_L1_proof SAP.P001e.WH.W4.T93_L2_proof
