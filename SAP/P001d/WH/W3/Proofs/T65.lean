import SAP.P001d.WH.W3.Leaves
import SAP.P001d.WH.W3.P.T65_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001d.WH.W3.T65_whole : SAP.P001d.T65WholeStatement :=
  SAP.P001d.WH.W3.T65_assembly SAP.P001d.WH.W3.T65_L1_proof
