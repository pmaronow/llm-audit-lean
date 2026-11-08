import SAP.P002b.WH.W1.Leaves
import SAP.P002b.WH.W1.P.T26_L1
import SAP.P002b.WH.W1.P.T26_L2
import SAP.P002b.WH.W1.P.T26_L3
import SAP.P002b.WH.W1.P.T26_L4
import SAP.P002b.WH.W1.P.T26_L5
import SAP.P002b.WH.W1.P.T26_L6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P002b.WH.W1.T26_whole : SAP.P002b.T26WholeStatement :=
  SAP.P002b.WH.W1.T26_assembly SAP.P002b.WH.W1.T26_L1_proof SAP.P002b.WH.W1.T26_L2_proof SAP.P002b.WH.W1.T26_L3_proof SAP.P002b.WH.W1.T26_L4_proof SAP.P002b.WH.W1.T26_L5_proof SAP.P002b.WH.W1.T26_L6_proof
