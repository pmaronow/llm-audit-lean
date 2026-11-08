import SAP.P003a.WH.W2.Leaves
import SAP.P003a.WH.W2.P.T14_L1
import SAP.P003a.WH.W2.P.T14_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003a.WH.W2.T14_whole : SAP.P003a.T14WholeStatement :=
  SAP.P003a.WH.W2.T14_assembly SAP.P003a.WH.W2.T14_L1_proof SAP.P003a.WH.W2.T14_L2_proof
