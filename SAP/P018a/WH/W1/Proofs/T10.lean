import SAP.P018a.WH.W1.Leaves
import SAP.P018a.WH.W1.P.T10_L1
import SAP.P018a.WH.W1.P.T10_L2
import SAP.P018a.WH.W1.P.T10_L3
import SAP.P018a.WH.W1.P.T10_L4
import SAP.P018a.WH.W1.P.T10_L5
import SAP.P018a.WH.W1.P.T10_L6
import SAP.P018a.WH.W1.P.T10_L7

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P018a.WH.W1.T10_whole : SAP.P018a.T10WholeStatement :=
  SAP.P018a.WH.W1.T10_assembly SAP.P018a.WH.W1.T10_L1_proof SAP.P018a.WH.W1.T10_L2_proof SAP.P018a.WH.W1.T10_L3_proof SAP.P018a.WH.W1.T10_L4_proof SAP.P018a.WH.W1.T10_L5_proof SAP.P018a.WH.W1.T10_L6_proof SAP.P018a.WH.W1.T10_L7_proof
