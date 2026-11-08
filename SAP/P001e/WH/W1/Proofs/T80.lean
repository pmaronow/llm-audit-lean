import SAP.P001e.WH.W1.Leaves
import SAP.P001e.WH.W1.P.T80_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001e.WH.W1.T80_whole : SAP.P001e.T80WholeStatement :=
  SAP.P001e.WH.W1.T80_assembly SAP.P001e.WH.W1.T80_L1_proof
