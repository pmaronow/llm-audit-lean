import SAP.P001d.WH.W2.Leaves
import SAP.P001d.WH.W2.P.T58_L1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001d.WH.W2.T58_whole : SAP.P001d.T58WholeStatement :=
  SAP.P001d.WH.W2.T58_assembly SAP.P001d.WH.W2.T58_L1_proof
