import SAP.P006a.WH.W1.Leaves
import SAP.P006a.WH.W1.P.T12_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P006a.WH.W1.T12_whole : SAP.P006a.T12WholeStatement :=
  SAP.P006a.WH.W1.T12_assembly SAP.P006a.WH.W1.T12_L1_proof
