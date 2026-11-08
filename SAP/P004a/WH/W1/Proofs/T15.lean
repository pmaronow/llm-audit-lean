import SAP.P004a.WH.W1.Leaves
import SAP.P004a.WH.W1.P.T15_L1
import SAP.P004a.WH.W1.P.T15_L2
import SAP.P004a.WH.W1.P.T15_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004a.WH.W1.T15_whole : SAP.P004a.T15WholeStatement.{u,v} :=
  SAP.P004a.WH.W1.T15_assembly.{u,v} SAP.P004a.WH.W1.T15_L1_proof SAP.P004a.WH.W1.T15_L2_proof SAP.P004a.WH.W1.T15_L3_proof
