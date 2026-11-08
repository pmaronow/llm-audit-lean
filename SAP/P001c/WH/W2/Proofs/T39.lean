import SAP.P001c.WH.W2.Leaves
import SAP.P001c.WH.W2.P.T39_L1
import SAP.P001c.WH.W2.P.T39_L2
import SAP.P001c.WH.W2.P.T39_L3
import SAP.P001c.WH.W2.P.T39_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001c.WH.W2.T39_whole : SAP.P001c.T39WholeStatement :=
  SAP.P001c.WH.W2.T39_assembly SAP.P001c.WH.W2.T39_L1_proof SAP.P001c.WH.W2.T39_L2_proof SAP.P001c.WH.W2.T39_L3_proof SAP.P001c.WH.W2.T39_L4_proof
