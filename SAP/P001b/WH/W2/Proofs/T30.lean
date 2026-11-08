import SAP.P001b.WH.W2.Leaves
import SAP.P001b.WH.W2.P.T30_L1
import SAP.P001b.WH.W2.P.T30_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001b.WH.W2.T30_whole : SAP.P001b.T30WholeStatement :=
  SAP.P001b.WH.W2.T30_assembly SAP.P001b.WH.W2.T30_L1_proof SAP.P001b.WH.W2.T30_L2_proof
