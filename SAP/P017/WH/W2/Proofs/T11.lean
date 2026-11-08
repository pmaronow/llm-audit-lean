import SAP.P017.WH.W2.Leaves
import SAP.P017.WH.W2.P.T11_L1
import SAP.P017.WH.W2.P.T11_L2
import SAP.P017.WH.W2.P.T11_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P017.WH.W2.T11_whole : SAP.P017.T11WholeStatement :=
  SAP.P017.WH.W2.T11_assembly SAP.P017.WH.W2.T11_L1_proof SAP.P017.WH.W2.T11_L2_proof SAP.P017.WH.W2.T11_L3_proof
