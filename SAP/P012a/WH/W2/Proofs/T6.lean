import SAP.P012a.WH.W2.Leaves
import SAP.P012a.WH.W2.P.T6_L1
import SAP.P012a.WH.W2.P.T6_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P012a.WH.W2.T6_whole : SAP.P012a.T6WholeStatement :=
  SAP.P012a.WH.W2.T6_assembly SAP.P012a.WH.W2.T6_L1_proof SAP.P012a.WH.W2.T6_L2_proof
