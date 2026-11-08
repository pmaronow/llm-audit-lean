import SAP.P012a.WH.W1.Leaves
import SAP.P012a.WH.W1.P.T11_L1
import SAP.P012a.WH.W1.P.T11_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P012a.WH.W1.T11_whole : SAP.P012a.T11WholeStatement :=
  SAP.P012a.WH.W1.T11_assembly SAP.P012a.WH.W1.T11_L1_proof SAP.P012a.WH.W1.T11_L2_proof
