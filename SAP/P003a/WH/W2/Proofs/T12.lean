import SAP.P003a.WH.W2.Leaves
import SAP.P003a.WH.W2.P.T12_L1
import SAP.P003a.WH.W2.P.T12_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003a.WH.W2.T12_whole : SAP.P003a.T12WholeStatement :=
  SAP.P003a.WH.W2.T12_assembly SAP.P003a.WH.W2.T12_L1_proof SAP.P003a.WH.W2.T12_L2_proof
