import SAP.P018a.WH.W2.Leaves
import SAP.P018a.WH.W2.P.T12_L1
import SAP.P018a.WH.W2.P.T12_L2
import SAP.P018a.WH.W2.P.T12_L3
import SAP.P018a.WH.W2.P.T12_L4
import SAP.P018a.WH.W2.P.T12_L5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P018a.WH.W2.T12_whole : SAP.P018a.T12WholeStatement :=
  SAP.P018a.WH.W2.T12_assembly SAP.P018a.WH.W2.T12_L1_proof SAP.P018a.WH.W2.T12_L2_proof SAP.P018a.WH.W2.T12_L3_proof SAP.P018a.WH.W2.T12_L4_proof SAP.P018a.WH.W2.T12_L5_proof
