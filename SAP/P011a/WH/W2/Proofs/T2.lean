import SAP.P011a.WH.W2.Leaves
import SAP.P011a.WH.W2.P.T2_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P011a.WH.W2.T2_whole : SAP.P011a.T2WholeStatement :=
  SAP.P011a.WH.W2.T2_assembly SAP.P011a.WH.W2.T2_L1_proof
