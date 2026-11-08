import SAP.P046.WH.W1.Leaves
import SAP.P046.WH.W1.P.T5_L1
import SAP.P046.WH.W1.P.T5_L2
import SAP.P046.WH.W1.P.T5_L3
import SAP.P046.WH.W1.P.T5_L4
import SAP.P046.WH.W1.P.T5_L5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P046.WH.W1.T5_whole : SAP.P046.T5WholeStatement :=
  SAP.P046.WH.W1.T5_assembly SAP.P046.WH.W1.T5_L1_proof SAP.P046.WH.W1.T5_L2_proof SAP.P046.WH.W1.T5_L3_proof SAP.P046.WH.W1.T5_L4_proof SAP.P046.WH.W1.T5_L5_proof
