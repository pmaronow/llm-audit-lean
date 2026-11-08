import SAP.P025a.WH.W2.Leaves
import SAP.P025a.WH.W2.P.T5_L1
import SAP.P025a.WH.W2.P.T5_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P025a.WH.W2.T5_whole : SAP.P025a.T5WholeStatement :=
  SAP.P025a.WH.W2.T5_assembly SAP.P025a.WH.W2.T5_L1_proof SAP.P025a.WH.W2.T5_L2_proof
