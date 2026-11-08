import SAP.P018a.WH.W2.Leaves
import SAP.P018a.WH.W2.P.T3_L1
import SAP.P018a.WH.W2.P.T3_L2
import SAP.P018a.WH.W2.P.T3_L3
import SAP.P018a.WH.W2.P.T3_L4
import SAP.P018a.WH.W2.P.T3_L5
import SAP.P018a.WH.W2.P.T3_L6
import SAP.P018a.WH.W2.P.T3_L7

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P018a.WH.W2.T3_whole : SAP.P018a.T3WholeStatement :=
  SAP.P018a.WH.W2.T3_assembly SAP.P018a.WH.W2.T3_L1_proof SAP.P018a.WH.W2.T3_L2_proof SAP.P018a.WH.W2.T3_L3_proof SAP.P018a.WH.W2.T3_L4_proof SAP.P018a.WH.W2.T3_L5_proof SAP.P018a.WH.W2.T3_L6_proof SAP.P018a.WH.W2.T3_L7_proof
