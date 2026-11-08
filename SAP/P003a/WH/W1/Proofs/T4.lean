import SAP.P003a.WH.W1.Leaves
import SAP.P003a.WH.W1.P.T4_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003a.WH.W1.T4_whole : SAP.P003a.T4WholeStatement :=
  SAP.P003a.WH.W1.T4_assembly SAP.P003a.WH.W1.T4_L1_proof
