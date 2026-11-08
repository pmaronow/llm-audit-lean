import SAP.P004b.WH.W2.Leaves
import SAP.P004b.WH.W2.P.T18_L1
import SAP.P004b.WH.W2.P.T18_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004b.WH.W2.T18_whole : SAP.P004b.T18WholeStatement :=
  SAP.P004b.WH.W2.T18_assembly SAP.P004b.WH.W2.T18_L1_proof SAP.P004b.WH.W2.T18_L2_proof
