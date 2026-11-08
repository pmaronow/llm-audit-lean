import SAP.P001f.WH.W1.Leaves
import SAP.P001f.WH.W1.P.T97_L1
import SAP.P001f.WH.W1.P.T97_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001f.WH.W1.T97_whole : SAP.P001f.T97WholeStatement :=
  SAP.P001f.WH.W1.T97_assembly SAP.P001f.WH.W1.T97_L1_proof SAP.P001f.WH.W1.T97_L2_proof
