import SAP.P001c.WH.W1.Leaves
import SAP.P001c.WH.W1.P.T57_L1
import SAP.P001c.WH.W1.P.T57_L2
import SAP.P001c.WH.W1.P.T57_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001c.WH.W1.T57_whole : SAP.P001c.T57WholeStatement :=
  SAP.P001c.WH.W1.T57_assembly SAP.P001c.WH.W1.T57_L1_proof SAP.P001c.WH.W1.T57_L2_proof SAP.P001c.WH.W1.T57_L3_proof
