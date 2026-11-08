import SAP.P027b.WH.W1.Leaves
import SAP.P027b.WH.W1.P.T14_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P027b.WH.W1.T14_whole : SAP.P027b.T14WholeStatement :=
  SAP.P027b.WH.W1.T14_assembly SAP.P027b.WH.W1.T14_L1_proof
