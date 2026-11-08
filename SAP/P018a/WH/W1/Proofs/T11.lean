import SAP.P018a.WH.W1.Leaves
import SAP.P018a.WH.W1.P.T11_L1
import SAP.P018a.WH.W1.P.T11_L2
import SAP.P018a.WH.W1.P.T11_L3
import SAP.P018a.WH.W1.P.T11_L4
import SAP.P018a.WH.W1.P.T11_L5
import SAP.P018a.WH.W1.P.T11_L6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P018a.WH.W1.T11_whole : SAP.P018a.T11WholeStatement :=
  SAP.P018a.WH.W1.T11_assembly SAP.P018a.WH.W1.T11_L1_proof SAP.P018a.WH.W1.T11_L2_proof SAP.P018a.WH.W1.T11_L3_proof SAP.P018a.WH.W1.T11_L4_proof SAP.P018a.WH.W1.T11_L5_proof SAP.P018a.WH.W1.T11_L6_proof
