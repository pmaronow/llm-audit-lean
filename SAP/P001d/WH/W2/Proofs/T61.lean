import SAP.P001d.WH.W2.Leaves
import SAP.P001d.WH.W2.P.T61_L1
import SAP.P001d.WH.W2.P.T61_L2
import SAP.P001d.WH.W2.P.T61_L3
import SAP.P001d.WH.W2.P.T61_L4
import SAP.P001d.WH.W2.P.T61_L5
import SAP.P001d.WH.W2.P.T61_L6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001d.WH.W2.T61_whole : SAP.P001d.T61WholeStatement :=
  SAP.P001d.WH.W2.T61_assembly SAP.P001d.WH.W2.T61_L1_proof SAP.P001d.WH.W2.T61_L2_proof SAP.P001d.WH.W2.T61_L3_proof SAP.P001d.WH.W2.T61_L4_proof SAP.P001d.WH.W2.T61_L5_proof SAP.P001d.WH.W2.T61_L6_proof
