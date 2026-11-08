import SAP.P001g.WH.W2.Leaves
import SAP.P001g.WH.W2.P.T121_L1
import SAP.P001g.WH.W2.P.T121_L2
import SAP.P001g.WH.W2.P.T121_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001g.WH.W2.T121_whole : SAP.P001g.T121WholeStatement :=
  SAP.P001g.WH.W2.T121_assembly SAP.P001g.WH.W2.T121_L1_proof SAP.P001g.WH.W2.T121_L2_proof SAP.P001g.WH.W2.T121_L3_proof
