import AronowAudit.P006.Wave1.CorrectedRankingBlueprint

set_option autoImplicit false
universe u v
namespace AronowAudit.P006.Wave1.CorrectedRanking
open AronowAudit.P006 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
noncomputable section

theorem n5_proof : N5.{u,v} := by
  classical
  intro h4 Ω C _ _ n E P0 _ hS hac hτ hU hreward
  have hτm : Measurable E.τ := hS.means_measurable.2.sub hS.means_measurable.1
  have hstar : Admissible (positiveRule E.τ) := by
    refine ⟨?_, ?_⟩
    · exact Measurable.ite (measurableSet_lt measurable_const hτm) measurable_const measurable_const
    · intro x
      by_cases h : 0 < E.τ x <;> simp [positiveRule, h]
  have hid (π : C → ℝ) (hπ : Admissible π) :
      E.expectedWeightedTT (referenceWeight n P0 E.PX) π = ∫ x, E.τ x * π x ∂P0 :=
    (h4 E P0 hS hac hτ hU hreward π hπ).1.trans
      (h4 E P0 hS hac hτ hU hreward π hπ).2
  have hint (π : C → ℝ) (hπ : Admissible π) : Integrable (fun x => E.τ x * π x) P0 := by
    apply hτ.mul_bdd hπ.1.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hπ.2 x).1]
      exact (hπ.2 x).2)
  have hpart : Integrable (fun x => positivePart (E.τ x)) P0 := by
    simpa only [positivePart_eq_max] using hτ.pos_part
  have hstarval : E.expectedWeightedTT (referenceWeight n P0 E.PX) (positiveRule E.τ) =
      ∫ x, positivePart (E.τ x) ∂P0 := by
    rw [hid _ hstar]
    rfl
  have hbest : IsBest {π | Admissible π}
      (E.expectedWeightedTT (referenceWeight n P0 E.PX)) (positiveRule E.τ) := by
    refine ⟨hstar, ?_⟩
    intro π hπ
    rw [hid π hπ, hstarval]
    exact integral_mono (hint π hπ) hpart (fun x => pointwise_policy_gain_le _ _ (hπ.2 x))
  exact ⟨hbest, (bestValue_eq hbest).trans hstarval⟩

end
end AronowAudit.P006.Wave1.CorrectedRanking
