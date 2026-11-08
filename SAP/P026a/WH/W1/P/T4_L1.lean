import SAP.P026a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P026a.WH.W1.P.T4_L1

open scoped BigOperators

end SAP.P026a.WH.W1.P.T4_L1

theorem SAP.P026a.WH.W1.T4_L1_proof : SAP.P026a.WH.W1.T4_L1 := by
  intro i j
  constructor
  · intro hind
    by_contra hpair
    have hc := hind (fun b : Bool => if b then (1 : ℚ) else 0)
      (fun b : Bool => if b then (1 : ℚ) else 0)
    fin_cases i <;> fin_cases j
    all_goals norm_num at hpair
    all_goals norm_num [mean, xorSixLaw, Fin.sum_univ_succ] at hc
  · intro hpair u v
    fin_cases i <;> fin_cases j
    all_goals norm_num at hpair
    all_goals simp [mean, xorSixLaw, Fin.sum_univ_succ]
    all_goals ring
