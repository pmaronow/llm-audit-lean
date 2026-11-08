import SAP.P001a.WH.W1.Leaves
import SAP.P001a.WH.W1.P.T4_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001a.WH.W1.T4_whole : SAP.P001a.T4WholeStatement :=
  SAP.P001a.WH.W1.T4_assembly SAP.P001a.WH.W1.T4_L1_proof
