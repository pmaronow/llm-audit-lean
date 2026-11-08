import SAP.P003a.WH.W3.Leaves
import SAP.P003a.WH.W3.P.T15_L1
import SAP.P003a.WH.W3.P.T15_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003a.WH.W3.T15_whole : SAP.P003a.T15WholeStatement :=
  SAP.P003a.WH.W3.T15_assembly SAP.P003a.WH.W3.T15_L1_proof SAP.P003a.WH.W3.T15_L2_proof
