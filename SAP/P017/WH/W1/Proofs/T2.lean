import SAP.P017.WH.W1.Leaves
import SAP.P017.WH.W1.P.T2_L1
import SAP.P017.WH.W1.P.T2_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P017.WH.W1.T2_whole : SAP.P017.T2WholeStatement :=
  SAP.P017.WH.W1.T2_assembly SAP.P017.WH.W1.T2_L1_proof SAP.P017.WH.W1.T2_L2_proof
