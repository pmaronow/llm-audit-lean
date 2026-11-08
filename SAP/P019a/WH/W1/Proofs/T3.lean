import SAP.P019a.WH.W1.Leaves
import SAP.P019a.WH.W1.P.T3_L1
import SAP.P019a.WH.W1.P.T3_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P019a.WH.W1.T3_whole : SAP.P019a.T3WholeStatement :=
  SAP.P019a.WH.W1.T3_assembly SAP.P019a.WH.W1.T3_L1_proof SAP.P019a.WH.W1.T3_L2_proof
