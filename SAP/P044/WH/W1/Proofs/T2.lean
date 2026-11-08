import SAP.P044.WH.W1.Leaves
import SAP.P044.WH.W1.P.T2_L1
import SAP.P044.WH.W1.P.T2_L2
import SAP.P044.WH.W1.P.T2_L3
import SAP.P044.WH.W1.P.T2_L4
import SAP.P044.WH.W1.P.T2_L5
import SAP.P044.WH.W1.P.T2_L6
import SAP.P044.WH.W1.P.T2_L7
import SAP.P044.WH.W1.P.T2_L8

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P044.WH.W1.T2_whole : SAP.P044.T2WholeStatement :=
  SAP.P044.WH.W1.T2_assembly SAP.P044.WH.W1.T2_L1_proof SAP.P044.WH.W1.T2_L2_proof SAP.P044.WH.W1.T2_L3_proof SAP.P044.WH.W1.T2_L4_proof SAP.P044.WH.W1.T2_L5_proof SAP.P044.WH.W1.T2_L6_proof SAP.P044.WH.W1.T2_L7_proof SAP.P044.WH.W1.T2_L8_proof
