import SAP.P009b.WH.W2.Leaves
import SAP.P009b.WH.W2.P.T26_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P009b.WH.W2.T26_whole : SAP.P009b.T26WholeStatement :=
  SAP.P009b.WH.W2.T26_assembly SAP.P009b.WH.W2.T26_L1_proof
