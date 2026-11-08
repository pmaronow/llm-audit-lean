import SAP.P008b.WH.W1.Leaves
import SAP.P008b.WH.W1.P.T26_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P008b.WH.W1.T26_whole : SAP.P008b.T26WholeStatement :=
  SAP.P008b.WH.W1.T26_assembly SAP.P008b.WH.W1.T26_L1_proof
