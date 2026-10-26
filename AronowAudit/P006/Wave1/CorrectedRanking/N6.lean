import AronowAudit.P006.Wave1.CorrectedRankingBlueprint

set_option autoImplicit false
universe u v
namespace AronowAudit.P006.Wave1.CorrectedRanking
open AronowAudit.P006 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
noncomputable section

theorem n6_proof : N6.{u} := by
  intro K C _ P0 score τ hτ hbest
  have hp (k : Fin K) : Integrable (fun x => positivePart (τ k x)) P0 := by
    simpa only [positivePart_eq_max] using (hτ k).pos_part
  refine ⟨?_, ?_⟩
  · intro j k horder
    rw [hbest k, hbest j]
    exact T14_corrected_rank_inequality P0 (τ j) (τ k) horder (hp j) (hp k)
  · intro hnonneg
    have hvalue (k : Fin K) : bestValue {π : C → ℝ | Admissible π} (score k) =
        ∫ x, τ k x ∂P0 := by
      rw [hbest k]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        show positivePart (τ k x) = τ k x
        rw [positivePart_eq_max, max_eq_left (hnonneg k x)])
    refine ⟨hvalue, ?_⟩
    intro j k horder
    rw [hvalue k, hvalue j]
    exact horder

end
end AronowAudit.P006.Wave1.CorrectedRanking
