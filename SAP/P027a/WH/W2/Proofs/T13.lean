import SAP.P027a.WH.W2.Leaves
import SAP.P027a.WH.W2.P.T13_L1
import SAP.P027a.WH.W2.P.T13_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P027a.WH.W2.T13_whole : SAP.P027a.T13WholeStatement :=
  SAP.P027a.WH.W2.T13_assembly SAP.P027a.WH.W2.T13_L1_proof SAP.P027a.WH.W2.T13_L2_proof
