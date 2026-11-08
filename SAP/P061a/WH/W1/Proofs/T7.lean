import SAP.P061a.WH.W1.Leaves
import SAP.P061a.WH.W1.P.T7_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P061a.WH.W1.T7_whole : SAP.P061a.T7WholeStatement :=
  SAP.P061a.WH.W1.T7_assembly SAP.P061a.WH.W1.T7_L1_proof
