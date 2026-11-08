import AronowAudit.P004.Wave1.AreaSumBlueprint

/-! Node A11 of the T5 area blueprint (trivial arithmetic; written by the blueprint architect):
the band-6 AME of the area-weighted share table is `121/18000`. -/

namespace AronowAudit.P004.Wave1.AreaSum
open AronowAudit.P004

theorem a11_proof : A11 := by
  norm_num [A11, ame, nodeEffect, marginal, expect, designWeight, coin, assignment_two_univ,
    binShare, Fin.sum_univ_succ]

end AronowAudit.P004.Wave1.AreaSum
