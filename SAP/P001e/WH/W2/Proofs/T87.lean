import SAP.P001e.WH.W2.Assemblies
import SAP.P001e.WH.W2.P.T87_L1
import SAP.P001e.WH.W2.P.T87_L2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P001e.WH.W2.T87_whole : SAP.P001e.T87WholeStatement :=
  SAP.P001e.WH.W2.T87_assembly SAP.P001e.WH.W2.T87_L1_proof SAP.P001e.WH.W2.T87_L2_proof
