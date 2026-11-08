import SAP.P026a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a.WH.W1.P.T1_L1

end SAP.P026a.WH.W1.P.T1_L1

theorem SAP.P026a.WH.W1.T1_L1_proof : SAP.P026a.WH.W1.T1_L1 := by
  unfold SAP.P026a.WH.W1.T1_L1 SAP.P026a.w1SixSupportFacts
  decide +kernel
