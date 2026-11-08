import SAP.P004b.WH.W2.Leaves
import SAP.P004b.WH.W2.P.T20_L1
import SAP.P004b.WH.W2.P.T20_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004b.WH.W2.T20_whole : SAP.P004b.T20WholeStatement :=
  SAP.P004b.WH.W2.T20_assembly SAP.P004b.WH.W2.T20_L1_proof SAP.P004b.WH.W2.T20_L2_proof
