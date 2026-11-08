import AronowAudit.P006.Wave1.Gap.Fid2P006

namespace AronowAudit.P006.Wave1.Fid2P006Contracts

set_option autoImplicit false
universe u v

open AronowAudit.P006 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
noncomputable section

/-- Approved statement: `~/lean-work/runs/map-fid2-P006/map.json`, record 0
(`P006-T13`, `proposed_statement_lean`), accepted without fixes by
`ref1-fid2-P006` and `ref2-fid2-P006`. -/
def approvedContract_T13 : Prop :=
  ∀ {K : ℕ} {C : Type u} [MeasurableSpace C] {Ω : Fin K → Type v}
    [∀ k, MeasurableSpace (Ω k)]
    (nk : Fin K → ℕ) (E : (k : Fin K) → Experiment (Ω k) C (nk k))
    (P0 : Measure C) (hP0 : IsProbabilityMeasure P0)
    (hD : ∀ k, T13_OutcomeStanding (E k))
    (hmu0 : ∀ j k, (E j).μ0 = (E k).μ0)
    (hac : ∀ k, P0 ≪ (E k).PX)
    (hτ : ∀ k, Integrable (E k).τ P0)
    (hR : ∀ k π, Admissible π → ∀ i,
      Integrable (fun ω => bit ((E k).T π i ω) *
        ((E k).μhat π ω ((E k).X i ω) -
          (E k).μ0 ((E k).X i ω))) ((E k).law π))
    (hU : ∀ k, TreatedUnbiased (E k) (E k).μ0 {π | Admissible π})
    (hreward : ∀ k π, Admissible π → ∀ i,
      Integrable (fun ω => ((E k).observed π ω i -
        (E k).μhat π ω ((E k).X i ω)) * bit ((E k).T π i ω) *
        referenceWeight (nk k) P0 (E k).PX ((E k).X i ω)) ((E k).law π)),
    (∀ k π, Admissible π →
      (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX) π =
        (nk k : ℝ) * (∫ x, (E k).τ x * π x *
          referenceWeight (nk k) P0 (E k).PX x ∂(E k).PX) ∧
      (nk k : ℝ) * (∫ x, (E k).τ x * π x *
          referenceWeight (nk k) P0 (E k).PX x ∂(E k).PX) =
        (∫ x, (E k).τ x * π x ∂P0)) ∧
    (∀ k, IsBest {π | Admissible π}
      ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
      (positiveRule (E k).τ) ∧
      bestValue {π | Admissible π}
        ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX)) =
        (∫ x, positivePart ((E k).τ x) ∂P0)) ∧
    UniformRankPreservation (fun _ => {π | Admissible π})
      (fun k => (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
      (fun k => (E k).τ) ∧
    ((∀ k x, 0 ≤ (E k).τ x) →
      (∀ k, bestValue {π | Admissible π}
        ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX)) =
        (∫ x, (E k).τ x ∂P0)) ∧
      RelativeRankPreservation P0 (fun _ => {π | Admissible π})
        (fun k => (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
        (fun k => (E k).τ))

example : approvedContract_T13 := @AronowAudit.P006.Wave1.T13_corrected_ranking_treated_residuals

/-- `map-fid2-P006/map.json`, record 0, `definition_body_lean` is a structure.
Its complete constructor is checked against every approved field type, in order.
Only the structure-field syntax is changed to lambda-binder syntax. -/
example {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) :
    @AronowAudit.P006.Wave1.T13_OutcomeStanding.mk Ω C _ _ n E =
      (fun
        (px_probability : IsProbabilityMeasure E.PX)
        (means_measurable : Measurable E.μ0 ∧ Measurable E.μ1)
        (means_integrable : Integrable E.μ0 E.PX ∧ Integrable E.μ1 E.PX)
        (law_probability : ∀ π, Admissible π → IsProbabilityMeasure (E.law π))
        (measurable_units : ∀ π, Admissible π → ∀ i,
    Measurable (E.X i) ∧ Measurable (E.Y0 i) ∧ Measurable (E.Y1 i) ∧
    Measurable (E.T π i))
        (integrable_units : ∀ π, Admissible π → ∀ i,
    Integrable (E.Y0 i) (E.law π) ∧ Integrable (E.Y1 i) (E.law π))
        (covariate_law : ∀ π, Admissible π → ∀ i,
    IdentDistrib (E.X i) (fun x : C => x) (E.law π) E.PX)
        (potential_law_fixed : ∀ π π', Admissible π → Admissible π' → ∀ i,
    IdentDistrib (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω))
      (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω)) (E.law π) (E.law π'))
        (iid_independent : ∀ π, Admissible π →
    iIndepFun (fun i ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω, E.T π i ω)) (E.law π))
        (iid_identical : ∀ π, Admissible π → ∀ i j,
    IdentDistrib (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω, E.T π i ω))
      (fun ω => (E.X j ω, E.Y0 j ω, E.Y1 j ω, E.T π j ω)) (E.law π) (E.law π))
        (conditional_means : ∀ π, Admissible π → ∀ i,
    (E.law π)[E.Y0 i | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => E.μ0 (E.X i ω)) ∧
    (E.law π)[E.Y1 i | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => E.μ1 (E.X i ω)))
        (bernoulli : ∀ π, Admissible π → ∀ i,
    (E.law π)[(fun ω => bit (E.T π i ω)) | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => π (E.X i ω)))
        (ignorability : ∀ π, Admissible π → ∀ i (B : Set (ℝ × ℝ)), MeasurableSet B →
    (E.law π)[(fun ω => bit (E.T π i ω) *
      B.indicator (fun _ => (1 : ℝ)) (E.Y0 i ω, E.Y1 i ω)) | E.covariateSigma i]
      =ᵐ[E.law π] (fun ω => π (E.X i ω) *
        (E.law π)[(fun η => B.indicator (fun _ => (1 : ℝ))
          (E.Y0 i η, E.Y1 i η)) | E.covariateSigma i] ω))
        => (⟨px_probability, means_measurable, means_integrable, law_probability, measurable_units, integrable_units, covariate_law, potential_law_fixed, iid_independent, iid_identical, conditional_means, bernoulli, ignorability⟩ :
          AronowAudit.P006.Wave1.T13_OutcomeStanding E)) := rfl

#print axioms AronowAudit.P006.Wave1.T13_corrected_ranking_treated_residuals

end
end AronowAudit.P006.Wave1.Fid2P006Contracts
