import SAP.P002a.WH.W3.Leaves
import SAP.P002a.WH.W3.P.T6_L1
import SAP.P002a.WH.W3.P.T6_L2
import SAP.P002a.WH.W3.P.T6_L3
import SAP.P002a.WH.W3.P.T6_L4
import SAP.P002a.WH.W3.P.T6_L5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P002a.WH.W3.T6_whole : SAP.P002a.T6WholeStatement :=
  SAP.P002a.WH.W3.T6_assembly SAP.P002a.WH.W3.T6_L1_proof SAP.P002a.WH.W3.T6_L2_proof SAP.P002a.WH.W3.T6_L3_proof SAP.P002a.WH.W3.T6_L4_proof SAP.P002a.WH.W3.T6_L5_proof
