import SAP.P003a.WH.W3.Leaves
import SAP.P003a.WH.W3.P.T17_L1
import SAP.P003a.WH.W3.P.T17_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003a.WH.W3.T17_whole : SAP.P003a.T17WholeStatement :=
  SAP.P003a.WH.W3.T17_assembly SAP.P003a.WH.W3.T17_L1_proof SAP.P003a.WH.W3.T17_L2_proof
