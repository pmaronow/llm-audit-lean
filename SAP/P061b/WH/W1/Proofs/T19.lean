import SAP.P061b.WH.W1.Leaves
import SAP.P061b.WH.W1.P.T19_L1
import SAP.P061b.WH.W1.P.T19_L2
import SAP.P061b.WH.W1.P.T19_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P061b.WH.W1.T19_whole : SAP.P061b.T19WholeStatement :=
  SAP.P061b.WH.W1.T19_assembly SAP.P061b.WH.W1.T19_L1_proof SAP.P061b.WH.W1.T19_L2_proof SAP.P061b.WH.W1.T19_L3_proof
