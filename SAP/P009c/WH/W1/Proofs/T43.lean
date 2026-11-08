import SAP.P009c.WH.W1.Leaves
import SAP.P009c.WH.W1.P.T41_L1
import SAP.P009c.WH.W1.P.T41_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P009c.WH.W1.T43_whole : SAP.P009c.T43WholeStatement :=
  SAP.P009c.WH.W1.T43_assembly SAP.P009c.WH.W1.T41_L1_proof SAP.P009c.WH.W1.T41_L2_proof
