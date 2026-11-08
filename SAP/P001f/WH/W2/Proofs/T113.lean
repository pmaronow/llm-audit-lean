import SAP.P001f.WH.W2.Leaves
import SAP.P001f.WH.W2.P.T113_L1
import SAP.P001f.WH.W2.P.T113_L2
import SAP.P001f.WH.W2.P.T113_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001f.WH.W2.T113_whole : SAP.P001f.T113WholeStatement :=
  SAP.P001f.WH.W2.T113_assembly SAP.P001f.WH.W2.T113_L1_proof SAP.P001f.WH.W2.T113_L2_proof SAP.P001f.WH.W2.T113_L3_proof
