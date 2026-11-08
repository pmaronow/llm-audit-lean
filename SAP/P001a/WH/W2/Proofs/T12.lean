import SAP.P001a.WH.W2.Leaves
import SAP.P001a.WH.W2.P.T12_L1
import SAP.P001a.WH.W2.P.T12_L2
import SAP.P001a.WH.W2.P.T12_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001a.WH.W2.T12_whole : SAP.P001a.T12WholeStatement :=
  SAP.P001a.WH.W2.T12_assembly SAP.P001a.WH.W2.T12_L1_proof SAP.P001a.WH.W2.T12_L2_proof SAP.P001a.WH.W2.T12_L3_proof
