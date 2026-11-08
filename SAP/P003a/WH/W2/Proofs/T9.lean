import SAP.P003a.WH.W2.Leaves
import SAP.P003a.WH.W2.P.T9_L1
import SAP.P003a.WH.W2.P.T9_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003a.WH.W2.T9_whole : SAP.P003a.T9WholeStatement :=
  SAP.P003a.WH.W2.T9_assembly SAP.P003a.WH.W2.T9_L1_proof SAP.P003a.WH.W2.T9_L2_proof
