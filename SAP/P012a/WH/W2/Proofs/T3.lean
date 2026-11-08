import SAP.P012a.WH.W2.Leaves
import SAP.P012a.WH.W2.P.T3_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P012a.WH.W2.T3_whole : SAP.P012a.T3WholeStatement :=
  SAP.P012a.WH.W2.T3_assembly SAP.P012a.WH.W2.T3_L1_proof
