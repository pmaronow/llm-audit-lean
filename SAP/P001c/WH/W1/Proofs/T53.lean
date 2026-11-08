import SAP.P001c.WH.W1.Leaves
import SAP.P001c.WH.W1.P.T53_L1
import SAP.P001c.WH.W1.P.T53_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001c.WH.W1.T53_whole : SAP.P001c.T53WholeStatement :=
  SAP.P001c.WH.W1.T53_assembly SAP.P001c.WH.W1.T53_L1_proof SAP.P001c.WH.W1.T53_L2_proof
