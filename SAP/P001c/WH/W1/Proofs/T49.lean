import SAP.P001c.WH.W1.Leaves
import SAP.P001c.WH.W1.P.T49_L1
import SAP.P001c.WH.W1.P.T49_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001c.WH.W1.T49_whole : SAP.P001c.T49WholeStatement :=
  SAP.P001c.WH.W1.T49_assembly SAP.P001c.WH.W1.T49_L1_proof SAP.P001c.WH.W1.T49_L2_proof
