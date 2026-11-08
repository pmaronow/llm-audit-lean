import SAP.P006b.WH.W1.Leaves
import SAP.P006b.WH.W1.P.T25_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P006b.WH.W1.T25_whole : SAP.P006b.T25WholeStatement :=
  SAP.P006b.WH.W1.T25_assembly SAP.P006b.WH.W1.T25_L1_proof
