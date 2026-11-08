import AronowAudit.P027.Wave1.CancellationLimitBlueprint

/-! Normalize the pointwise negative-square identity for the actual design bias. -/

namespace AronowAudit.P027.Wave1.CancellationLimit

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
attribute [local instance] Classical.propDecidable

theorem n2_proof : N2 := by
  intro r m hr hm Ξ β ε ξ
  have hK : 0 < Fintype.card (Σ _ : Fin r × Fin 2, Fin m) := by
    simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
    positivity
  have hA : biasA (phaseOriginal r m hr) (centeredOutcomes phaseSize β ε ξ) =
      -∑ g : Fin r × Fin 2,
        (groupTotal (fun _ => m) (centeredOutcomes phaseSize β ε ξ) g)^2 :=
    (periodic_negative_square r m hr (centeredOutcomes phaseSize β ε ξ)
      (centered_outcomes_zero hK phaseSize β ε ξ)).2.1
  rw [hA, neg_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  rw [← div_pow, phase_centered_total_formula r m hr hm, add_div]
  rfl

end
end AronowAudit.P027.Wave1.CancellationLimit
