import SAP.P004a.WH.W1.Leaves
import SAP.P004a.WH.W1.P.T5_L1
import SAP.P004a.WH.W1.P.T5_L2
import SAP.P004a.WH.W1.P.T5_L3
import SAP.P004a.WH.W1.P.T5_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004a.WH.W1.T5_whole : SAP.P004a.T5WholeStatement :=
  SAP.P004a.WH.W1.T5_assembly SAP.P004a.WH.W1.T5_L1_proof SAP.P004a.WH.W1.T5_L2_proof SAP.P004a.WH.W1.T5_L3_proof SAP.P004a.WH.W1.T5_L4_proof
