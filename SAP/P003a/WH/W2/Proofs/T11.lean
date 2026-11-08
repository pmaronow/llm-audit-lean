import SAP.P003a.WH.W2.Leaves
import SAP.P003a.WH.W2.P.T11_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003a.WH.W2.T11_whole : SAP.P003a.T11WholeStatement :=
  SAP.P003a.WH.W2.T11_assembly SAP.P003a.WH.W2.T11_L1_proof
