import SAP.P001e.WH.W2.Assemblies
import SAP.P001e.WH.W2.P.T94_L1
import SAP.P001e.WH.W2.P.T94_L2
import SAP.P001e.WH.W2.P.T94_L3
import SAP.P001e.WH.W2.P.T94_L4
import SAP.P001e.WH.W2.P.T94_L5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001e.WH.W2.T94_whole : SAP.P001e.T94WholeStatement :=
  SAP.P001e.WH.W2.T94_assembly SAP.P001e.WH.W2.T94_L1_proof SAP.P001e.WH.W2.T94_L2_proof SAP.P001e.WH.W2.T94_L3_proof SAP.P001e.WH.W2.T94_L4_proof SAP.P001e.WH.W2.T94_L5_proof
