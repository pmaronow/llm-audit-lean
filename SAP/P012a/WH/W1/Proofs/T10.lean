import SAP.P012a.WH.W1.Leaves
import SAP.P012a.WH.W1.P.T10_L1
import SAP.P012a.WH.W1.P.T10_L2
import SAP.P012a.WH.W1.P.T10_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P012a.WH.W1.T10_whole : SAP.P012a.T10WholeStatement :=
  SAP.P012a.WH.W1.T10_assembly SAP.P012a.WH.W1.T10_L1_proof SAP.P012a.WH.W1.T10_L2_proof SAP.P012a.WH.W1.T10_L3_proof
