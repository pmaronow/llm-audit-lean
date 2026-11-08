import AronowAudit.P027.Wave1.AggregationRationaleBlueprint

namespace AronowAudit.P027.Wave1.AggregationRationale

set_option autoImplicit false
noncomputable section
open AronowAudit.P027
attribute [local instance] Classical.propDecidable

/-- At group level the outcomes are `(2,1)`, giving `A = 4` and `A* = 5`. -/
theorem n2_proof : N2 := by
  have hY (g : Fin 2) : groupTotal nW yW g = (nW g : ℝ) := by
    simp only [groupTotal, yW, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  constructor
  · norm_num [biasA, hY, nW, joint, expect, indicator, cluster2, Fin.sum_univ_two]
  · norm_num [quadraticA, hY, nW, joint, expect, indicator, cluster2, Fin.sum_univ_two]

end
end AronowAudit.P027.Wave1.AggregationRationale
