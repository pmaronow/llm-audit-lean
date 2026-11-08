import SAP.P002a.WH.W2.Leaves
import SAP.P002a.WH.W2.P.T2_L1
import SAP.P002a.WH.W2.P.T2_L2
import SAP.P002a.WH.W2.P.T2_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P002a.WH.W2.T2_whole : SAP.P002a.T2WholeStatement :=
  SAP.P002a.WH.W2.T2_assembly SAP.P002a.WH.W2.T2_L1_proof SAP.P002a.WH.W2.T2_L2_proof SAP.P002a.WH.W2.T2_L3_proof
