import SAP.P001b.WH.W1.Leaves
import SAP.P001b.WH.W1.P.T27_L1
import SAP.P001b.WH.W1.P.T27_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001b.WH.W1.T27_whole : SAP.P001b.T27WholeStatement :=
  SAP.P001b.WH.W1.T27_assembly SAP.P001b.WH.W1.T27_L1_proof SAP.P001b.WH.W1.T27_L2_proof
