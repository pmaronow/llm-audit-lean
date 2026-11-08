import SAP.P001d.WH.W1.Leaves
import SAP.P001d.WH.W1.P.T74_L1V2
import SAP.P001d.WH.W1.P.T74_L2V2
import SAP.P001d.WH.W1.P.T74_L3V2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001d.WH.W1.T74_whole : SAP.P001d.T74WholeStatement :=
  SAP.P001d.WH.W1.T74_assembly SAP.P001d.WH.W1.T74_L1V2_proof SAP.P001d.WH.W1.T74_L2V2_proof SAP.P001d.WH.W1.T74_L3V2_proof
