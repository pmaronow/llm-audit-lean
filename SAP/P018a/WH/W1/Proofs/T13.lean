import SAP.P018a.WH.W1.Leaves
import SAP.P018a.WH.W1.P.T13_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P018a.WH.W1.T13_whole : SAP.P018a.T13WholeStatement :=
  SAP.P018a.WH.W1.T13_assembly SAP.P018a.WH.W1.T13_L1_proof
