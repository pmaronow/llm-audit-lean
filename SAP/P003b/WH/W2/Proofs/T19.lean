import SAP.P003b.WH.W2.Leaves
import SAP.P003b.WH.W2.P.T19_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003b.WH.W2.T19_whole : SAP.P003b.T19WholeStatement :=
  SAP.P003b.WH.W2.T19_assembly SAP.P003b.WH.W2.T19_L1_proof
