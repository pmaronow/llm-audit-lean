import SAP.P002a.WH.W2.Leaves
import SAP.P002a.WH.W2.P.T4_L1
import SAP.P002a.WH.W2.P.T4_L2
import SAP.P002a.WH.W2.P.T4_L3
import SAP.P002a.WH.W2.P.T4_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P002a.WH.W2.T4_whole : SAP.P002a.T4WholeStatement :=
  SAP.P002a.WH.W2.T4_assembly SAP.P002a.WH.W2.T4_L1_proof SAP.P002a.WH.W2.T4_L2_proof SAP.P002a.WH.W2.T4_L3_proof SAP.P002a.WH.W2.T4_L4_proof
