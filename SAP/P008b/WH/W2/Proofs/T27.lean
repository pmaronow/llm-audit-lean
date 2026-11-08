import SAP.P008b.WH.W2.Leaves
import SAP.P008b.WH.W2.P.T27_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P008b.WH.W2.T27_whole : SAP.P008b.T27WholeStatement :=
  SAP.P008b.WH.W2.T27_assembly SAP.P008b.WH.W2.T27_L1_proof
