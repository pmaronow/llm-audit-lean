import SAP.P012a.WH.W1.Leaves
import SAP.P012a.WH.W1.P.T1_L1
import SAP.P012a.WH.W1.P.T1_L2
import SAP.P012a.WH.W1.P.T1_L3
import SAP.P012a.WH.W1.P.T1_L4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P012a.WH.W1.T1_whole : SAP.P012a.T1WholeStatement :=
  SAP.P012a.WH.W1.T1_assembly SAP.P012a.WH.W1.T1_L1_proof SAP.P012a.WH.W1.T1_L2_proof SAP.P012a.WH.W1.T1_L3_proof SAP.P012a.WH.W1.T1_L4_proof
