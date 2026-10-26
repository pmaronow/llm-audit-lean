import AronowAudit.P004.Wave1.AreaSumBlueprint

/-! P004-T5: the band-6 AME of the area-weighted share table is `121/18000`. -/

namespace AronowAudit.P004.Wave1.AreaSum
open AronowAudit.P004

theorem a11_proof : A11 := by
  norm_num [A11, ame, nodeEffect, marginal, expect, designWeight, coin, assignment_two_univ,
    binShare, Fin.sum_univ_succ]

end AronowAudit.P004.Wave1.AreaSum
