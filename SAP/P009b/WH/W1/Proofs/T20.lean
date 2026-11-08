import SAP.P009b.WH.W1.Leaves
import SAP.P009b.WH.W1.P.T20_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P009b.WH.W1.T20_whole : SAP.P009b.T20WholeStatement :=
  SAP.P009b.WH.W1.T20_assembly SAP.P009b.WH.W1.T20_L1_proof
