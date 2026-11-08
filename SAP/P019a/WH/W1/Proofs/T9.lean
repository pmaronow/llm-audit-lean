import SAP.P019a.WH.W1.Leaves
import SAP.P019a.WH.W1.P.T9_L1
import SAP.P019a.WH.W1.P.T9_L2
import SAP.P019a.WH.W1.P.T9_L3
import SAP.P019a.WH.W1.P.T9_L4
import SAP.P019a.WH.W1.P.T9_L5
import SAP.P019a.WH.W1.P.T9_L6
import SAP.P019a.WH.W1.P.T9_L7

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P019a.WH.W1.T9_whole : SAP.P019a.T9WholeStatement :=
  SAP.P019a.WH.W1.T9_assembly SAP.P019a.WH.W1.T9_L1_proof SAP.P019a.WH.W1.T9_L2_proof SAP.P019a.WH.W1.T9_L3_proof SAP.P019a.WH.W1.T9_L4_proof SAP.P019a.WH.W1.T9_L5_proof SAP.P019a.WH.W1.T9_L6_proof SAP.P019a.WH.W1.T9_L7_proof
