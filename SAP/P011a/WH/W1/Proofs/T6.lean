import SAP.P011a.WH.W1.Leaves
import SAP.P011a.WH.W1.P.T6_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P011a.WH.W1.T6_whole : SAP.P011a.T6WholeStatement :=
  SAP.P011a.WH.W1.T6_assembly SAP.P011a.WH.W1.T6_L1_proof
