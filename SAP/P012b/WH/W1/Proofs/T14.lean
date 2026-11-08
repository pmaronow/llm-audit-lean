import SAP.P012b.WH.W1.Leaves
import SAP.P012b.WH.W1.P.T14_L1
import SAP.P012b.WH.W1.P.T14_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P012b.WH.W1.T14_whole : SAP.P012b.T14WholeStatement :=
  SAP.P012b.WH.W1.T14_assembly SAP.P012b.WH.W1.T14_L1_proof SAP.P012b.WH.W1.T14_L2_proof
