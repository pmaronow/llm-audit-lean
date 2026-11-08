import SAP.P018a.WH.W2.Leaves
import SAP.P018a.WH.W2.P.T1_L1
import SAP.P018a.WH.W2.P.T1_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P018a.WH.W2.T1_whole : SAP.P018a.T1WholeStatement :=
  SAP.P018a.WH.W2.T1_assembly SAP.P018a.WH.W2.T1_L1_proof SAP.P018a.WH.W2.T1_L2_proof
