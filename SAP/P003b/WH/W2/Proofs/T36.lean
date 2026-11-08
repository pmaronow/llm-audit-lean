import SAP.P003b.WH.W2.Leaves
import SAP.P003b.WH.W2.P.T36_L1
import SAP.P003b.WH.W2.P.T36_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003b.WH.W2.T36_whole : SAP.P003b.T36WholeStatement :=
  SAP.P003b.WH.W2.T36_assembly SAP.P003b.WH.W2.T36_L1_proof SAP.P003b.WH.W2.T36_L2_proof
