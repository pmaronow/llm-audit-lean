import SAP.P046.WH.W1.Leaves
import SAP.P046.WH.W1.P.T3_L1
import SAP.P046.WH.W1.P.T3_L2
import SAP.P046.WH.W1.P.T3_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P046.WH.W1.T3_whole : SAP.P046.T3WholeStatement :=
  SAP.P046.WH.W1.T3_assembly SAP.P046.WH.W1.T3_L1_proof SAP.P046.WH.W1.T3_L2_proof SAP.P046.WH.W1.T3_L3_proof
