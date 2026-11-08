import SAP.P003b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W1.P.T6_L1

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem finiteCount : SAP.P003b.WH.W1.T6_L1 := by
  unfold SAP.P003b.WH.W1.T6_L1
  decide +kernel

end SAP.P003b.WH.W1.P.T6_L1

theorem SAP.P003b.WH.W1.T6_L1_proof : SAP.P003b.WH.W1.T6_L1 :=
  SAP.P003b.WH.W1.P.T6_L1.finiteCount
