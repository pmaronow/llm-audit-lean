import SAP.P001a.WH.W3.Leaves
import SAP.P001a.WH.W3.P.T5_L1
import SAP.P001a.WH.W3.P.T5_L2
import SAP.P001a.WH.W3.P.T5_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001a.WH.W3.T5_whole : SAP.P001a.T5WholeStatement_W3 :=
  SAP.P001a.WH.W3.T5_assembly SAP.P001a.WH.W3.T5_L1_proof SAP.P001a.WH.W3.T5_L2_proof SAP.P001a.WH.W3.T5_L3_proof
