import SAP.P009b.WH.W2.Leaves
import SAP.P009b.WH.W2.P.T22_L1
import SAP.P009b.WH.W2.P.T22_L2
import SAP.P009b.WH.W2.P.T22_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P009b.WH.W2.T22_whole : SAP.P009b.T22WholeStatement :=
  SAP.P009b.WH.W2.T22_assembly SAP.P009b.WH.W2.T22_L1_proof SAP.P009b.WH.W2.T22_L2_proof SAP.P009b.WH.W2.T22_L3_proof
