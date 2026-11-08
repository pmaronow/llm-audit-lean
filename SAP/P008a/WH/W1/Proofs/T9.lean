import SAP.P008a.WH.W1.Leaves
import SAP.P008a.WH.W1.P.T9_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P008a.WH.W1.T9_whole : SAP.P008a.T9WholeStatement :=
  SAP.P008a.WH.W1.T9_assembly SAP.P008a.WH.W1.T9_L1_proof
