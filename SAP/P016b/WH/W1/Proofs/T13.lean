import SAP.P016b.WH.W1.Leaves
import SAP.P016b.WH.W1.P.T13_L1
import SAP.P016b.WH.W1.P.T13_L2
import SAP.P016b.WH.W1.P.T13_L3
import SAP.P016b.WH.W1.P.T13_L4
import SAP.P016b.WH.W1.P.T13_L5
import SAP.P016b.WH.W1.P.T13_L6
import SAP.P016b.WH.W1.P.T13_L7
import SAP.P016b.WH.W1.P.T13_L8

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Generated assembly of the whole statement from its proved leaves. -/
theorem SAP.P016b.WH.W1.T13_whole : SAP.P016b.T13WholeStatement :=
  SAP.P016b.WH.W1.T13_assembly SAP.P016b.WH.W1.T13_L1_proof SAP.P016b.WH.W1.T13_L2_proof SAP.P016b.WH.W1.T13_L3_proof SAP.P016b.WH.W1.T13_L4_proof SAP.P016b.WH.W1.T13_L5_proof SAP.P016b.WH.W1.T13_L6_proof SAP.P016b.WH.W1.T13_L7_proof SAP.P016b.WH.W1.T13_L8_proof
