import SAP.P015b.WH.W2.Leaves
import SAP.P015b.WH.W2.P.T22_L1
import SAP.P015b.WH.W2.P.T22_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P015b.WH.W2.T15_whole : SAP.P015b.T15WholeStatement :=
  SAP.P015b.WH.W2.T15_assembly SAP.P015b.WH.W2.T22_L1_proof SAP.P015b.WH.W2.T22_L2_proof
