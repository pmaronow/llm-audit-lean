import SAP.P025b.WH.W1.Leaves
import SAP.P025b.WH.W1.P.T15_L1
import SAP.P025b.WH.W1.P.T15_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P025b.WH.W1.T15_whole : SAP.P025b.T15WholeStatement :=
  SAP.P025b.WH.W1.T15_assembly SAP.P025b.WH.W1.T15_L1_proof SAP.P025b.WH.W1.T15_L2_proof
