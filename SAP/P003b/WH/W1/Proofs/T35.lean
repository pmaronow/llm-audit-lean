import SAP.P003b.WH.W1.Leaves
import SAP.P003b.WH.W1.P.T35_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003b.WH.W1.T35_whole : SAP.P003b.T35WholeStatement :=
  SAP.P003b.WH.W1.T35_assembly SAP.P003b.WH.W1.T35_L1_proof
