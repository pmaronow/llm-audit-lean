import SAP.P001c.WH.W2.Leaves
import SAP.P001c.WH.W2.P.T43_L1
import SAP.P001c.WH.W2.P.T43_L2
import SAP.P001c.WH.W2.P.T43_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001c.WH.W2.T43_whole : SAP.P001c.T43WholeStatement :=
  SAP.P001c.WH.W2.T43_assembly SAP.P001c.WH.W2.T43_L1_proof SAP.P001c.WH.W2.T43_L2_proof SAP.P001c.WH.W2.T43_L3_proof
