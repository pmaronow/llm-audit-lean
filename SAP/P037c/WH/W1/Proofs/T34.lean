import SAP.P037c.WH.W1.Leaves
import SAP.P037c.WH.W1.P.T34_L1
import SAP.P037c.WH.W1.P.T34_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P037c.WH.W1.T34_whole : SAP.P037c.T34WholeStatement :=
  SAP.P037c.WH.W1.T34_assembly SAP.P037c.WH.W1.T34_L1_proof SAP.P037c.WH.W1.T34_L2_proof
