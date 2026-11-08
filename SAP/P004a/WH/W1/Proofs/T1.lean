import SAP.P004a.WH.W1.Leaves
import SAP.P004a.WH.W1.P.T1_L1
import SAP.P004a.WH.W1.P.T1_L2
import SAP.P004a.WH.W1.P.T1_L3
import SAP.P004a.WH.W1.P.T1_L4
import SAP.P004a.WH.W1.P.T1_L5
import SAP.P004a.WH.W1.P.T1_L6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004a.WH.W1.T1_whole : SAP.P004a.T1WholeStatement :=
  SAP.P004a.WH.W1.T1_assembly SAP.P004a.WH.W1.T1_L1_proof SAP.P004a.WH.W1.T1_L2_proof SAP.P004a.WH.W1.T1_L3_proof SAP.P004a.WH.W1.T1_L4_proof SAP.P004a.WH.W1.T1_L5_proof SAP.P004a.WH.W1.T1_L6_proof
