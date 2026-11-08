import SAP.P004b.WH.W1.Leaves
import SAP.P004b.WH.W1.P.T25_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004b.WH.W1.T25_whole : SAP.P004b.T25WholeStatement :=
  SAP.P004b.WH.W1.T25_assembly SAP.P004b.WH.W1.T25_L1_proof
