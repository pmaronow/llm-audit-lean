import SAP.P029b.WH.W2.Leaves
import SAP.P029b.WH.W2.P.T27_L1
import SAP.P029b.WH.W2.P.T27_L2
import SAP.P029b.WH.W2.P.T27_L3
import SAP.P029b.WH.W2.P.T27_L4
import SAP.P029b.WH.W2.P.T27_L5
import SAP.P029b.WH.W2.P.T27_L6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P029b.WH.W2.T27_whole : SAP.P029b.T27WholeStatement :=
  SAP.P029b.WH.W2.T27_assembly SAP.P029b.WH.W2.T27_L1_proof SAP.P029b.WH.W2.T27_L2_proof SAP.P029b.WH.W2.T27_L3_proof SAP.P029b.WH.W2.T27_L4_proof SAP.P029b.WH.W2.T27_L5_proof SAP.P029b.WH.W2.T27_L6_proof
