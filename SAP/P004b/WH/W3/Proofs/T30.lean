import SAP.P004b.WH.W3.Leaves
import SAP.P004b.WH.W3.P.T30_L1
import SAP.P004b.WH.W3.P.T30_L2
import SAP.P004b.WH.W3.P.T30_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004b.WH.W3.T30_whole : SAP.P004b.T30WholeStatement :=
  SAP.P004b.WH.W3.T30_assembly SAP.P004b.WH.W3.T30_L1_proof SAP.P004b.WH.W3.T30_L2_proof SAP.P004b.WH.W3.T30_L3_proof
