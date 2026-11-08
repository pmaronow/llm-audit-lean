import SAP.P001e.WH.W1.Leaves
import SAP.P001e.WH.W1.P.T78_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001e.WH.W1.T78_whole : SAP.P001e.T78WholeStatement :=
  SAP.P001e.WH.W1.T78_assembly SAP.P001e.WH.W1.T78_L1_proof
