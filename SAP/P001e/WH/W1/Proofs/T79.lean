import SAP.P001e.WH.W1.Leaves
import SAP.P001e.WH.W1.P.T79_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001e.WH.W1.T79_whole : SAP.P001e.T79WholeStatement :=
  SAP.P001e.WH.W1.T79_assembly SAP.P001e.WH.W1.T79_L1_proof
