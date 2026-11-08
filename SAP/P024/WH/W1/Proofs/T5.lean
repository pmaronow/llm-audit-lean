import SAP.P024.WH.W1.Leaves
import SAP.P024.WH.W1.P.T5_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P024.WH.W1.T5_whole : SAP.P024.T5WholeStatement :=
  SAP.P024.WH.W1.T5_assembly SAP.P024.WH.W1.T5_L1_proof
