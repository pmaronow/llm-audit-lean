import SAP.P037a.WH.W1.Leaves
import SAP.P037a.WH.W1.P.T3_L1
import SAP.P037a.WH.W1.P.T3_L2
import SAP.P037a.WH.W1.P.T3_L3
import SAP.P037a.WH.W1.P.T3_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P037a.WH.W1.T3_whole : SAP.P037a.T3WholeStatement :=
  SAP.P037a.WH.W1.T3_assembly SAP.P037a.WH.W1.T3_L1_proof SAP.P037a.WH.W1.T3_L2_proof SAP.P037a.WH.W1.T3_L3_proof SAP.P037a.WH.W1.T3_L4_proof
