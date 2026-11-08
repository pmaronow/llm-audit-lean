import SAP.P001a.WH.W2.Leaves
import SAP.P001a.WH.W2.P.T17_L1
import SAP.P001a.WH.W2.P.T17_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001a.WH.W2.T17_whole : SAP.P001a.T17WholeStatement :=
  SAP.P001a.WH.W2.T17_assembly SAP.P001a.WH.W2.T17_L1_proof SAP.P001a.WH.W2.T17_L2_proof
