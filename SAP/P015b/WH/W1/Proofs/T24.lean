import SAP.P015b.WH.W1.Leaves
import SAP.P015b.WH.W1.P.T24_L1
import SAP.P015b.WH.W1.P.T24_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P015b.WH.W1.T24_whole : SAP.P015b.T24WholeStatement :=
  SAP.P015b.WH.W1.T24_assembly SAP.P015b.WH.W1.T24_L1_proof SAP.P015b.WH.W1.T24_L2_proof
