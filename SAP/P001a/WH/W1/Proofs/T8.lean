import SAP.P001a.WH.W1.Leaves
import SAP.P001a.WH.W1.P.T8_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001a.WH.W1.T8_whole : SAP.P001a.T8WholeStatement :=
  SAP.P001a.WH.W1.T8_assembly SAP.P001a.WH.W1.T8_L1_proof
