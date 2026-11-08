import SAP.P019a.WH.W2.Leaves
import SAP.P019a.WH.W2.P.T11_L1
import SAP.P019a.WH.W2.P.T11_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P019a.WH.W2.T11_whole : SAP.P019a.T11WholeStatement :=
  SAP.P019a.WH.W2.T11_assembly SAP.P019a.WH.W2.T11_L1_proof SAP.P019a.WH.W2.T11_L2_proof
