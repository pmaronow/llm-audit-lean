import SAP.P002a.WH.W2.Leaves
import SAP.P002a.WH.W2.P.T14_L1
import SAP.P002a.WH.W2.P.T14_L2
import SAP.P002a.WH.W2.P.T14_L3
import SAP.P002a.WH.W2.P.T14_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P002a.WH.W2.T14_whole : SAP.P002a.T14WholeStatement :=
  SAP.P002a.WH.W2.T14_assembly SAP.P002a.WH.W2.T14_L1_proof SAP.P002a.WH.W2.T14_L2_proof SAP.P002a.WH.W2.T14_L3_proof SAP.P002a.WH.W2.T14_L4_proof
