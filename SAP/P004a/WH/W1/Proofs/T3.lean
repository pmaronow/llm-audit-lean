import SAP.P004a.WH.W1.Leaves
import SAP.P004a.WH.W1.P.T3_L1
import SAP.P004a.WH.W1.P.T3_L2
import SAP.P004a.WH.W1.P.T3_L3
import SAP.P004a.WH.W1.P.T3_L4
import SAP.P004a.WH.W1.P.T3_L5
import SAP.P004a.WH.W1.P.T3_L6
import SAP.P004a.WH.W1.P.T3_L7
import SAP.P004a.WH.W1.P.T3_L8

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004a.WH.W1.T3_whole : SAP.P004a.T3WholeStatement :=
  SAP.P004a.WH.W1.T3_assembly SAP.P004a.WH.W1.T3_L1_proof SAP.P004a.WH.W1.T3_L2_proof SAP.P004a.WH.W1.T3_L3_proof SAP.P004a.WH.W1.T3_L4_proof SAP.P004a.WH.W1.T3_L5_proof SAP.P004a.WH.W1.T3_L6_proof SAP.P004a.WH.W1.T3_L7_proof SAP.P004a.WH.W1.T3_L8_proof
