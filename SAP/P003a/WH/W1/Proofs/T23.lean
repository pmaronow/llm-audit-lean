import SAP.P003a.WH.W1.Leaves
import SAP.P003a.WH.W1.P.T23_L1
import SAP.P003a.WH.W1.P.T23_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003a.WH.W1.T23_whole : SAP.P003a.T23WholeStatement :=
  SAP.P003a.WH.W1.T23_assembly SAP.P003a.WH.W1.T23_L1_proof SAP.P003a.WH.W1.T23_L2_proof
