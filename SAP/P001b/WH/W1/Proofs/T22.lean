import SAP.P001b.WH.W1.Leaves
import SAP.P001b.WH.W1.P.T22_L1V2
import SAP.P001b.WH.W1.P.T22_L2V2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001b.WH.W1.T22_whole : SAP.P001b.T22WholeStatement :=
  SAP.P001b.WH.W1.T22_assembly SAP.P001b.WH.W1.T22_L1V2_proof SAP.P001b.WH.W1.T22_L2V2_proof
