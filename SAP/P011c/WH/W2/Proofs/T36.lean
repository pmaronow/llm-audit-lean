import SAP.P011c.WH.W2.Leaves
import SAP.P011c.WH.W2.P.T36_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P011c.WH.W2.T36_whole : SAP.P011c.T36WholeStatement :=
  SAP.P011c.WH.W2.T36_assembly SAP.P011c.WH.W2.T36_L1_proof
