import SAP.P018b.WH.W1.Leaves
import SAP.P018b.WH.W1.P.T17_L1
import SAP.P018b.WH.W1.P.T17_L2
import SAP.P018b.WH.W1.P.T17_L3
import SAP.P018b.WH.W1.P.T17_L4
import SAP.P018b.WH.W1.P.T17_L5
import SAP.P018b.WH.W1.P.T17_L6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P018b.WH.W1.T17_whole : SAP.P018b.T17WholeStatement :=
  SAP.P018b.WH.W1.T17_assembly SAP.P018b.WH.W1.T17_L1_proof SAP.P018b.WH.W1.T17_L2_proof SAP.P018b.WH.W1.T17_L3_proof SAP.P018b.WH.W1.T17_L4_proof SAP.P018b.WH.W1.T17_L5_proof SAP.P018b.WH.W1.T17_L6_proof
