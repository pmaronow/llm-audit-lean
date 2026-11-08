import SAP.P009c.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009c.WH.W1.P.T41_L2

end SAP.P009c.WH.W1.P.T41_L2

theorem SAP.P009c.WH.W1.T41_L2_proof : SAP.P009c.WH.W1.T41_L2 := by
  intro Ω _ P U V n hn
  let Q := SAP.P009c.Bridge.toLaw P
  change AronowAudit.P009.prob Q (fun z => U z = 0 ∨ V z = 0) ≤
    AronowAudit.P009.mean Q (fun z => (U z / n - 1) ^ 2) +
      AronowAudit.P009.mean Q (fun z => (V z / n - 1) ^ 2)
  calc
    AronowAudit.P009.prob Q (fun z => U z = 0 ∨ V z = 0)
        ≤ AronowAudit.P009.prob Q (fun z => 1 ≤ |U z / n - 1|) +
            AronowAudit.P009.prob Q (fun z => 1 ≤ |V z / n - 1|) := by
          apply AronowAudit.P009.probability_union_bound Q
            (fun z => U z = 0 ∨ V z = 0)
            (fun z => 1 ≤ |U z / n - 1|)
            (fun z => 1 ≤ |V z / n - 1|)
          intro z hz
          rcases hz with hU | hV
          · left
            simp [hU]
          · right
            simp [hV]
    _ ≤ AronowAudit.P009.mean Q (fun z => (U z / n - 1) ^ 2) +
          AronowAudit.P009.mean Q (fun z => (V z / n - 1) ^ 2) := by
          simpa using add_le_add
            (AronowAudit.P009.BernoulliCompletion.second_moment_tail Q
              (fun z => U z / n - 1) 1 (by norm_num))
            (AronowAudit.P009.BernoulliCompletion.second_moment_tail Q
              (fun z => V z / n - 1) 1 (by norm_num))
