import SAP.P037b.WH.W2.Leaves
import SAP.P037b.WH.W2.P.T22_L1
import SAP.P037b.WH.W2.P.T22_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P037b.WH.W2.T22_whole : SAP.P037b.T22WholeStatement_W2 :=
  SAP.P037b.WH.W2.T22_assembly SAP.P037b.WH.W2.T22_L1_proof SAP.P037b.WH.W2.T22_L2_proof
