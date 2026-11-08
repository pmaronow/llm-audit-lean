import SAP.P004a.WH.W2.Leaves
import SAP.P004a.WH.W2.P.T8_L1
import SAP.P004a.WH.W2.P.T8_L2
import SAP.P004a.WH.W2.P.T8_L3
import SAP.P004a.WH.W2.P.T8_L4
import SAP.P004a.WH.W2.P.T8_L5
import SAP.P004a.WH.W2.P.T8_L6
import SAP.P004a.WH.W2.P.T8_L7

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P004a.WH.W2.T8_whole : SAP.P004a.T8WholeStatement.{u} :=
  SAP.P004a.WH.W2.T8_assembly.{u} SAP.P004a.WH.W2.T8_L1_proof SAP.P004a.WH.W2.T8_L2_proof SAP.P004a.WH.W2.T8_L3_proof SAP.P004a.WH.W2.T8_L4_proof SAP.P004a.WH.W2.T8_L5_proof SAP.P004a.WH.W2.T8_L6_proof SAP.P004a.WH.W2.T8_L7_proof
