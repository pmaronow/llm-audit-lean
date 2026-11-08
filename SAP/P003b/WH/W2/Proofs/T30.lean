import SAP.P003b.WH.W2.Leaves
import SAP.P003b.WH.W2.P.T30_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P003b.WH.W2.T30_whole : SAP.P003b.T30WholeStatement :=
  SAP.P003b.WH.W2.T30_assembly SAP.P003b.WH.W2.T30_L1_proof
