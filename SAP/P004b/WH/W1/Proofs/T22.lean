import SAP.P004b.WH.W1.Leaves
import SAP.P004b.WH.W1.P.T22_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004b.WH.W1.T22_whole : SAP.P004b.T22WholeStatement :=
  SAP.P004b.WH.W1.T22_assembly SAP.P004b.WH.W1.T22_L1_proof
