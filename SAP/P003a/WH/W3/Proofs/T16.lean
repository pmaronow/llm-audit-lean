import SAP.P003a.WH.W3.Leaves
import SAP.P003a.WH.W3.P.T16_L1
import SAP.P003a.WH.W3.P.T16_L2
import SAP.P003a.WH.W3.P.T16_L3
import SAP.P003a.WH.W3.P.T16_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003a.WH.W3.T16_whole : SAP.P003a.T16WholeStatement :=
  SAP.P003a.WH.W3.T16_assembly SAP.P003a.WH.W3.T16_L1_proof SAP.P003a.WH.W3.T16_L2_proof SAP.P003a.WH.W3.T16_L3_proof SAP.P003a.WH.W3.T16_L4_proof
