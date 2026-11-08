import SAP.P001g.WH.W1.Leaves
import SAP.P001g.WH.W1.P.T117_L1V2
import SAP.P001g.WH.W1.P.T117_L2V2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001g.WH.W1.T117_whole : SAP.P001g.T117WholeStatement :=
  SAP.P001g.WH.W1.T117_assembly SAP.P001g.WH.W1.T117_L1V2_proof SAP.P001g.WH.W1.T117_L2V2_proof
