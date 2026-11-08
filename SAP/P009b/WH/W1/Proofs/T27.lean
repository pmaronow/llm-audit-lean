import SAP.P009b.WH.W1.Leaves
import SAP.P009b.WH.W1.P.T27_L1
import SAP.P009b.WH.W1.P.T27_L2
import SAP.P009b.WH.W1.P.T27_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P009b.WH.W1.T27_whole : SAP.P009b.T27WholeStatement :=
  SAP.P009b.WH.W1.T27_assembly SAP.P009b.WH.W1.T27_L1_proof SAP.P009b.WH.W1.T27_L2_proof SAP.P009b.WH.W1.T27_L3_proof
