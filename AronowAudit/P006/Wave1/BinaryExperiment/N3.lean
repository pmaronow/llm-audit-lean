import AronowAudit.P006.Wave1.BinaryExperimentBlueprint

set_option autoImplicit false
namespace AronowAudit.P006.Wave1.BinaryExperiment
open AronowAudit.P006 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section

/-- Reduction of a one-coordinate test to the four one-unit atoms. -/
lemma integral_eval (h1 : S1) (n : ℕ) (π : Bool → ℝ) (hπ : Admissible π)
    (i : Fin n) (f : Bool × Bool → ℝ) :
    (∫ ω, f (ω i) ∂(Measure.pi fun _ : Fin n => unitLaw π)) =
      ∑ x : Bool, ∑ t : Bool, ((1 / 2 : ℝ) * coinMass (π x) t) * f (x,t) := by
  haveI : IsProbabilityMeasure (unitLaw π) := (h1 π hπ).1
  have heval := (measurePreserving_eval (fun _ : Fin n => unitLaw π) i).map_eq
  calc
    _ = ∫ a, f a ∂unitLaw π := by
      have hint := integral_map (μ := Measure.pi fun _ : Fin n => unitLaw π)
        (measurable_pi_apply i).aemeasurable (measurable_of_finite f).aestronglyMeasurable
      rw [heval] at hint
      exact hint.symm
    _ = _ := by
      rw [integral_fintype (Integrable.of_finite : Integrable f (unitLaw π)),
        Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro t _
      rw [measureReal_def, (h1 π hπ).2.1, ENNReal.toReal_ofReal]
      · rfl
      · exact mul_nonneg (by norm_num) ((coin_is_probability _ (hπ.2 x)).1 t)

theorem n3_proof : N3 := by
  classical
  intro h1 n hn y1 μhat π hπ i g
  let E := binExp n hn y1 μhat
  let H : Bool → ℝ := fun x => ∑ t : Bool, coinMass (π x) t * g (x,t)
  haveI : IsProbabilityMeasure (unitLaw π) := (h1 π hπ).1
  haveI : IsProbabilityMeasure (E.law π) := by dsimp [E, binExp]; infer_instance
  have hm : E.covariateSigma i ≤ (inferInstance : MeasurableSpace (Fin n → Bool × Bool)) :=
    (measurable_of_finite (E.X i)).comap_le
  have hH : StronglyMeasurable[E.covariateSigma i] (fun ω => H (E.X i ω)) :=
    ((measurable_of_finite H).comp (comap_measurable (E.X i))).stronglyMeasurable
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm
    (Integrable.of_finite : Integrable (fun ω => g (ω i)) (E.law π))
  · intro s _ _
    exact (Integrable.of_finite : Integrable (fun ω => H (E.X i ω)) (E.law π)).integrableOn
  · intro s hs _
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have hs0 : MeasurableSet (E.X i ⁻¹' B) := (measurable_of_finite (E.X i)) hB
    rw [← integral_indicator hs0, ← integral_indicator hs0]
    have hl : (E.X i ⁻¹' B).indicator (fun ω => H (E.X i ω)) =
        fun ω => B.indicator H (ω i).1 := by
      funext ω
      simp [Set.indicator, E, binExp]
    have hr : (E.X i ⁻¹' B).indicator (fun ω => g (ω i)) =
        fun ω => (if (ω i).1 ∈ B then g (ω i) else 0) := by
      funext ω
      simp [Set.indicator, E, binExp]
    show (∫ ω, (E.X i ⁻¹' B).indicator (fun ω => H (E.X i ω)) ω ∂E.law π) =
      ∫ ω, (E.X i ⁻¹' B).indicator (fun ω => g (ω i)) ω ∂E.law π
    rw [hl, hr]
    change (∫ ω, B.indicator H (ω i).1 ∂(Measure.pi fun _ : Fin n => unitLaw π)) =
      ∫ ω, (fun a : Bool × Bool => if a.1 ∈ B then g a else 0) (ω i)
        ∂(Measure.pi fun _ : Fin n => unitLaw π)
    rw [integral_eval h1 n π hπ i (fun a => B.indicator H a.1),
      integral_eval h1 n π hπ i (fun a => if a.1 ∈ B then g a else 0)]
    simp only [Fintype.sum_bool, H, Set.indicator, coinMass]
    by_cases h0 : false ∈ B <;> by_cases h1 : true ∈ B <;> simp [h0, h1] <;> ring
  · exact hH.aestronglyMeasurable

end
end AronowAudit.P006.Wave1.BinaryExperiment
