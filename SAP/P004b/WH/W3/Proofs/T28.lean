import SAP.P004b.WH.W3.Leaves
import SAP.P004b.WH.W3.P.T28_L1
import SAP.P004b.WH.W3.P.T28_L2
import SAP.P004b.WH.W3.P.T28_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004b.WH.W3.T28_whole : SAP.P004b.T28WholeStatement :=
  SAP.P004b.WH.W3.T28_assembly SAP.P004b.WH.W3.T28_L1_proof SAP.P004b.WH.W3.T28_L2_proof SAP.P004b.WH.W3.T28_L3_proof
