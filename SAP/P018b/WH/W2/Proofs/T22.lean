import SAP.P018b.WH.W2.Leaves
import SAP.P018b.WH.W2.P.T22_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P018b.WH.W2.T22_whole : SAP.P018b.T22WholeStatement :=
  SAP.P018b.WH.W2.T22_assembly SAP.P018b.WH.W2.T22_L1_proof
