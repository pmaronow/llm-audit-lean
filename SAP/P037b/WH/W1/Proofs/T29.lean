import SAP.P037b.WH.W1.Leaves
import SAP.P037b.WH.W1.P.T29_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P037b.WH.W1.T29_whole : SAP.P037b.T29WholeStatement :=
  SAP.P037b.WH.W1.T29_assembly SAP.P037b.WH.W1.T29_L1_proof
