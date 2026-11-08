import SAP.P042.WH.W1.Leaves
import SAP.P042.WH.W1.P.T1_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P042.WH.W1.T1_whole : SAP.P042.T1WholeStatement :=
  SAP.P042.WH.W1.T1_assembly SAP.P042.WH.W1.T1_L1_proof
