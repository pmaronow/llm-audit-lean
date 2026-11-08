import SAP.P011b.WH.W1.Leaves
import SAP.P011b.WH.W1.P.T15_L1
import SAP.P011b.WH.W1.P.T15_L2
import SAP.P011b.WH.W1.P.T15_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P011b.WH.W1.T15_whole : SAP.P011b.T15WholeStatement :=
  SAP.P011b.WH.W1.T15_assembly SAP.P011b.WH.W1.T15_L1_proof SAP.P011b.WH.W1.T15_L2_proof SAP.P011b.WH.W1.T15_L3_proof
