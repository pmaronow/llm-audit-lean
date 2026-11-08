import SAP.P025b.WH.W1.Leaves
import SAP.P025b.WH.W1.P.T16_L1
import SAP.P025b.WH.W1.P.T16_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P025b.WH.W1.T16_whole : SAP.P025b.T16WholeStatement :=
  SAP.P025b.WH.W1.T16_assembly SAP.P025b.WH.W1.T16_L1_proof SAP.P025b.WH.W1.T16_L2_proof
