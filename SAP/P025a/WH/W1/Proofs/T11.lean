import SAP.P025a.WH.W1.Leaves
import SAP.P025a.WH.W1.P.T11_L1
import SAP.P025a.WH.W1.P.T11_L2
import SAP.P025a.WH.W1.P.T11_L3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P025a.WH.W1.T11_whole : SAP.P025a.T11WholeStatement :=
  SAP.P025a.WH.W1.T11_assembly SAP.P025a.WH.W1.T11_L1_proof SAP.P025a.WH.W1.T11_L2_proof SAP.P025a.WH.W1.T11_L3_proof
