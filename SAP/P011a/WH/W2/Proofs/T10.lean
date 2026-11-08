import SAP.P011a.WH.W2.Leaves
import SAP.P011a.WH.W2.P.T10_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P011a.WH.W2.T10_whole : SAP.P011a.T10WholeStatement :=
  SAP.P011a.WH.W2.T10_assembly SAP.P011a.WH.W2.T10_L1_proof
