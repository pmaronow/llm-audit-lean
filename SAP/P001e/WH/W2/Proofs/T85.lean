import SAP.P001e.WH.W2.Assemblies
import SAP.P001e.WH.W2.P.T85_L1
import SAP.P001e.WH.W2.P.T85_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001e.WH.W2.T85_whole : SAP.P001e.T85WholeStatement :=
  SAP.P001e.WH.W2.T85_assembly SAP.P001e.WH.W2.T85_L1_proof SAP.P001e.WH.W2.T85_L2_proof
