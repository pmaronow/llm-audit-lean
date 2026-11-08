import SAP.P010.WH.W1.Leaves
import SAP.P010.WH.W1.P.T12_L1
import SAP.P010.WH.W1.P.T12_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P010.WH.W1.T12_whole : SAP.P010.T12WholeStatement :=
  SAP.P010.WH.W1.T12_assembly SAP.P010.WH.W1.T12_L1_proof SAP.P010.WH.W1.T12_L2_proof
