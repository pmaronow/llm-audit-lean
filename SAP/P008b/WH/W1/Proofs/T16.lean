import SAP.P008b.WH.W1.Leaves
import SAP.P008b.WH.W1.P.T16_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P008b.WH.W1.T16_whole : SAP.P008b.T16WholeStatement :=
  SAP.P008b.WH.W1.T16_assembly SAP.P008b.WH.W1.T16_L1_proof
