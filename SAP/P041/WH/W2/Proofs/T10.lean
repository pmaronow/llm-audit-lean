import SAP.P041.WH.W2.Leaves
import SAP.P041.WH.W2.P.T10_L1
import SAP.P041.WH.W2.P.T10_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P041.WH.W2.T10_whole : SAP.P041.T10WholeStatement :=
  SAP.P041.WH.W2.T10_assembly SAP.P041.WH.W2.T10_L1_proof SAP.P041.WH.W2.T10_L2_proof
