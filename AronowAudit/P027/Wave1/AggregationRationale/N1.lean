import AronowAudit.P027.Wave1.AggregationRationaleBlueprint

namespace AronowAudit.P027.Wave1.AggregationRationale

set_option autoImplicit false
noncomputable section
open AronowAudit.P027
attribute [local instance] Classical.propDecidable

/-- All-one member outcomes have both total and square-sum equal to fibre size. -/
theorem n1_proof : N1 := by
  have hpos : Positive cluster2 := aggregation_counterexample_positive.2.1
  have hY (g : Fin 2) : groupTotal nW yW g = (nW g : ℝ) := by
    simp only [groupTotal, yW, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hS (g : Fin 2) : groupSquares nW yW g = (nW g : ℝ) := by
    simp only [groupSquares, yW, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  constructor
  · rw [aggregation_A_preserved cluster2 hpos nW yW]
    norm_num [biasA, hY, nW, joint, expect, indicator, cluster2, Fin.sum_univ_two]
  · rw [quadraticA_lift cluster2 hpos nW yW]
    norm_num [hS, nW, joint, expect, indicator, cluster2, Fin.sum_univ_two]

end
end AronowAudit.P027.Wave1.AggregationRationale
