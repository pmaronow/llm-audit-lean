import SAP.P004b.WH.W2.Leaves
import SAP.P004b.WH.W2.P.T16_L1
import SAP.P004b.WH.W2.P.T16_L2
import SAP.P004b.WH.W2.P.T16_L3
import SAP.P004b.WH.W2.P.T16_L4
import SAP.P004b.WH.W2.P.T16_L5
import SAP.P004b.WH.W2.P.T16_L6
import SAP.P004b.WH.W2.P.T16_L7

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004b.WH.W2.T16_whole : SAP.P004b.T16WholeStatement :=
  SAP.P004b.WH.W2.T16_assembly SAP.P004b.WH.W2.T16_L1_proof SAP.P004b.WH.W2.T16_L2_proof SAP.P004b.WH.W2.T16_L3_proof SAP.P004b.WH.W2.T16_L4_proof SAP.P004b.WH.W2.T16_L5_proof SAP.P004b.WH.W2.T16_L6_proof SAP.P004b.WH.W2.T16_L7_proof
