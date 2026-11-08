import SAP.P005a.WH.W1.Leaves
import SAP.P005a.WH.W1.P.T3_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P005a.WH.W1.T3_whole : SAP.P005a.T3WholeStatement :=
  SAP.P005a.WH.W1.T3_assembly SAP.P005a.WH.W1.T3_L1_proof
