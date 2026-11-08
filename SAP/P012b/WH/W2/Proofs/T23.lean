import SAP.P012b.WH.W2.Leaves
import SAP.P012b.WH.W2.P.T23_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P012b.WH.W2.T23_whole : SAP.P012b.T23WholeStatement :=
  SAP.P012b.WH.W2.T23_assembly SAP.P012b.WH.W2.T23_L1_proof
