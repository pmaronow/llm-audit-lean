import SAP.P011c.WH.W1.Leaves
import SAP.P011c.WH.W1.P.T38_L1
import SAP.P011c.WH.W1.P.T39_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P011c.WH.W1.T39_whole : SAP.P011c.T39WholeStatement :=
  SAP.P011c.WH.W1.T39_assembly SAP.P011c.WH.W1.T38_L1_proof SAP.P011c.WH.W1.T39_L1_proof
