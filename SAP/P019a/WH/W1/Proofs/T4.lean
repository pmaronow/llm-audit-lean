import SAP.P019a.WH.W1.Leaves
import SAP.P019a.WH.W1.P.T4_L1
import SAP.P019a.WH.W1.P.T4_L2
import SAP.P019a.WH.W1.P.T4_L3
import SAP.P019a.WH.W1.P.T4_L4
import SAP.P019a.WH.W1.P.T4_L5
import SAP.P019a.WH.W1.P.T4_L6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P019a.WH.W1.T4_whole : SAP.P019a.T4WholeStatement :=
  SAP.P019a.WH.W1.T4_assembly SAP.P019a.WH.W1.T4_L1_proof SAP.P019a.WH.W1.T4_L2_proof SAP.P019a.WH.W1.T4_L3_proof SAP.P019a.WH.W1.T4_L4_proof SAP.P019a.WH.W1.T4_L5_proof SAP.P019a.WH.W1.T4_L6_proof
