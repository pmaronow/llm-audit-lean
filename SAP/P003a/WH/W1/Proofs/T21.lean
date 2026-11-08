import SAP.P003a.WH.W1.Leaves
import SAP.P003a.WH.W1.P.T21_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003a.WH.W1.T21_whole : SAP.P003a.T21WholeStatement :=
  SAP.P003a.WH.W1.T21_assembly SAP.P003a.WH.W1.T21_L1_proof
