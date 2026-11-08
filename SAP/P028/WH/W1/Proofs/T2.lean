import SAP.P028.WH.W1.Leaves
import SAP.P028.WH.W1.P.T2_L1
import SAP.P028.WH.W1.P.T2_L2
import SAP.P028.WH.W1.P.T2_L3
import SAP.P028.WH.W1.P.T2_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P028.WH.W1.T2_whole : SAP.P028.T2WholeStatement :=
  SAP.P028.WH.W1.T2_assembly SAP.P028.WH.W1.T2_L1_proof SAP.P028.WH.W1.T2_L2_proof SAP.P028.WH.W1.T2_L3_proof SAP.P028.WH.W1.T2_L4_proof
