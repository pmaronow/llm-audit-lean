import SAP.P004b.WH.W1.Leaves
import SAP.P004b.WH.W1.P.T26_L1
import SAP.P004b.WH.W1.P.T26_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004b.WH.W1.T26_whole : SAP.P004b.T26WholeStatement :=
  SAP.P004b.WH.W1.T26_assembly SAP.P004b.WH.W1.T26_L1_proof SAP.P004b.WH.W1.T26_L2_proof
