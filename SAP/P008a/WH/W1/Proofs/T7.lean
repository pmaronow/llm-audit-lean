import SAP.P008a.WH.W1.Leaves
import SAP.P008a.WH.W1.P.T7_L1
import SAP.P008a.WH.W1.P.T7_L2
import SAP.P008a.WH.W1.P.T7_L3
import SAP.P008a.WH.W1.P.T7_L4
import SAP.P008a.WH.W1.P.T7_L5
import SAP.P008a.WH.W1.P.T7_L6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P008a.WH.W1.T7_whole : SAP.P008a.T7WholeStatement :=
  SAP.P008a.WH.W1.T7_assembly SAP.P008a.WH.W1.T7_L1_proof SAP.P008a.WH.W1.T7_L2_proof SAP.P008a.WH.W1.T7_L3_proof SAP.P008a.WH.W1.T7_L4_proof SAP.P008a.WH.W1.T7_L5_proof SAP.P008a.WH.W1.T7_L6_proof
