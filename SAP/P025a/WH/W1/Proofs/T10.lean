import SAP.P025a.WH.W1.Leaves
import SAP.P025a.WH.W1.P.T10_L1
import SAP.P025a.WH.W1.P.T10_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P025a.WH.W1.T10_whole : SAP.P025a.T10WholeStatement :=
  SAP.P025a.WH.W1.T10_assembly SAP.P025a.WH.W1.T10_L1_proof SAP.P025a.WH.W1.T10_L2_proof
