import SAP.P011a.WH.W2.Leaves
import SAP.P011a.WH.W2.P.T3_L1
import SAP.P011a.WH.W2.P.T3_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P011a.WH.W2.T3_whole : SAP.P011a.T3WholeStatement :=
  SAP.P011a.WH.W2.T3_assembly SAP.P011a.WH.W2.T3_L1_proof SAP.P011a.WH.W2.T3_L2_proof
