import SAP.P018b.WH.W1.Leaves
import SAP.P018b.WH.W1.P.T20_L1
import SAP.P018b.WH.W1.P.T20_L2
import SAP.P018b.WH.W1.P.T20_L3
import SAP.P018b.WH.W1.P.T20_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P018b.WH.W1.T20_whole : SAP.P018b.T20WholeStatement :=
  SAP.P018b.WH.W1.T20_assembly SAP.P018b.WH.W1.T20_L1_proof SAP.P018b.WH.W1.T20_L2_proof SAP.P018b.WH.W1.T20_L3_proof SAP.P018b.WH.W1.T20_L4_proof
