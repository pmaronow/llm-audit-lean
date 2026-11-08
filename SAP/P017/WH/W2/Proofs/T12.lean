import SAP.P017.WH.W2.Leaves
import SAP.P017.WH.W2.P.T12_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P017.WH.W2.T12_whole : SAP.P017.T12WholeStatement :=
  SAP.P017.WH.W2.T12_assembly SAP.P017.WH.W2.T12_L1_proof
