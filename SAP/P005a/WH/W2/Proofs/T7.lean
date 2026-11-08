import SAP.P005a.WH.W2.Leaves
import SAP.P005a.WH.W2.P.T7_L1
import SAP.P005a.WH.W2.P.T7_L2
import SAP.P005a.WH.W2.P.T7_L3
import SAP.P005a.WH.W2.P.T7_L4
import SAP.P005a.WH.W2.P.T7_L5
import SAP.P005a.WH.W2.P.T7_L6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P005a.WH.W2.T7_whole : SAP.P005a.T7WholeStatement :=
  SAP.P005a.WH.W2.T7_assembly SAP.P005a.WH.W2.T7_L1_proof SAP.P005a.WH.W2.T7_L2_proof SAP.P005a.WH.W2.T7_L3_proof SAP.P005a.WH.W2.T7_L4_proof SAP.P005a.WH.W2.T7_L5_proof SAP.P005a.WH.W2.T7_L6_proof
