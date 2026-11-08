import SAP.P009b.WH.W3.Leaves
import SAP.P009b.WH.W3.P.T29_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P009b.WH.W3.T29_whole : SAP.P009b.T29WholeStatement_W3 :=
  SAP.P009b.WH.W3.T29_assembly SAP.P009b.WH.W3.T29_L1_proof
