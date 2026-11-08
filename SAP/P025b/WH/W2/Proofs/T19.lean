import SAP.P025b.WH.W2.Leaves
import SAP.P025b.WH.W2.P.T19_L1
import SAP.P025b.WH.W2.P.T19_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P025b.WH.W2.T19_whole : SAP.P025b.T19WholeStatement :=
  SAP.P025b.WH.W2.T19_assembly SAP.P025b.WH.W2.T19_L1_proof SAP.P025b.WH.W2.T19_L2_proof
