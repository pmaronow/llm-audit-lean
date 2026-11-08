import SAP.P003a.WH.W2.Leaves
import SAP.P003a.WH.W2.P.T5_L1
import SAP.P003a.WH.W2.P.T5_L2
import SAP.P003a.WH.W2.P.T5_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003a.WH.W2.T5_whole : SAP.P003a.T5WholeStatement :=
  SAP.P003a.WH.W2.T5_assembly SAP.P003a.WH.W2.T5_L1_proof SAP.P003a.WH.W2.T5_L2_proof SAP.P003a.WH.W2.T5_L3_proof
