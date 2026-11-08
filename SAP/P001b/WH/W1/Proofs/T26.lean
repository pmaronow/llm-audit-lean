import SAP.P001b.WH.W1.Leaves
import SAP.P001b.WH.W1.P.T26_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001b.WH.W1.T26_whole : SAP.P001b.T26WholeStatement :=
  SAP.P001b.WH.W1.T26_assembly SAP.P001b.WH.W1.T26_L1_proof
