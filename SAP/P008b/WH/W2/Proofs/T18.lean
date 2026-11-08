import SAP.P008b.WH.W2.Leaves
import SAP.P008b.WH.W2.P.T18_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P008b.WH.W2.T18_whole : SAP.P008b.T18WholeStatement :=
  SAP.P008b.WH.W2.T18_assembly SAP.P008b.WH.W2.T18_L1_proof
