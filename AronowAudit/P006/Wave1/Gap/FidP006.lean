import AronowAudit.P006.Wave1.Gap.GLP006B1

/-! The corrected average-reward theorem, with estimator assumptions confined to ATT. -/

namespace AronowAudit.P006.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance instDecidableFidP006 (p : Prop) : Decidable p := Classical.propDecidable p

/-- The outcome and design fields of `Standing`, without estimator integrability. -/
structure T2_OutcomeStanding {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) : Prop where
  px_probability : IsProbabilityMeasure E.PX
  means_measurable : Measurable E.μ0 ∧ Measurable E.μ1
  means_integrable : Integrable E.μ0 E.PX ∧ Integrable E.μ1 E.PX
  law_probability : ∀ π, Admissible π → IsProbabilityMeasure (E.law π)
  measurable_units : ∀ π, Admissible π → ∀ i,
    Measurable (E.X i) ∧ Measurable (E.Y0 i) ∧ Measurable (E.Y1 i) ∧
    Measurable (E.T π i)
  integrable_units : ∀ π, Admissible π → ∀ i,
    Integrable (E.Y0 i) (E.law π) ∧ Integrable (E.Y1 i) (E.law π)
  covariate_law : ∀ π, Admissible π → ∀ i,
    IdentDistrib (E.X i) (fun x : C => x) (E.law π) E.PX
  potential_law_fixed : ∀ π π', Admissible π → Admissible π' → ∀ i,
    IdentDistrib (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω))
      (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω)) (E.law π) (E.law π')
  iid_independent : ∀ π, Admissible π →
    iIndepFun (fun i ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω, E.T π i ω)) (E.law π)
  iid_identical : ∀ π, Admissible π → ∀ i j,
    IdentDistrib (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω, E.T π i ω))
      (fun ω => (E.X j ω, E.Y0 j ω, E.Y1 j ω, E.T π j ω)) (E.law π) (E.law π)
  conditional_means : ∀ π, Admissible π → ∀ i,
    (E.law π)[E.Y0 i | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => E.μ0 (E.X i ω)) ∧
    (E.law π)[E.Y1 i | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => E.μ1 (E.X i ω))
  bernoulli : ∀ π, Admissible π → ∀ i,
    (E.law π)[(fun ω => bit (E.T π i ω)) | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => π (E.X i ω))
  ignorability : ∀ π, Admissible π → ∀ i (B : Set (ℝ × ℝ)), MeasurableSet B →
    (E.law π)[(fun ω => bit (E.T π i ω) *
      B.indicator (fun _ => (1 : ℝ)) (E.Y0 i ω, E.Y1 i ω)) | E.covariateSigma i]
      =ᵐ[E.law π] (fun ω => π (E.X i ω) *
        (E.law π)[(fun η => B.indicator (fun _ => (1 : ℝ))
          (E.Y0 i η, E.Y1 i η)) | E.covariateSigma i] ω)

/-- A proof-only experiment whose estimator is the deterministic population baseline. -/
def T2_fid_baseline {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) : Experiment Ω C n :=
  { E with μhat := fun _ _ x => E.μ0 x }

lemma T2_fid_baseline_standing {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (hD : T2_OutcomeStanding E) :
    Standing (T2_fid_baseline E) := by
  refine {
    px_probability := hD.px_probability
    means_measurable := hD.means_measurable
    means_integrable := hD.means_integrable
    law_probability := hD.law_probability
    measurable_units := hD.measurable_units
    integrable_units := ?_
    covariate_law := hD.covariate_law
    potential_law_fixed := hD.potential_law_fixed
    iid_independent := hD.iid_independent
    iid_identical := hD.iid_identical
    conditional_means := hD.conditional_means
    bernoulli := hD.bernoulli
    ignorability := hD.ignorability }
  intro π hp i
  exact ⟨(hD.integrable_units π hp i).1, (hD.integrable_units π hp i).2,
    ((hD.covariate_law π hp i).comp hD.means_measurable.1).integrable_iff.mpr
      hD.means_integrable.1⟩

lemma T2_fid_baseline_vectorUnbiased {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (hD : T2_OutcomeStanding E) :
    VectorUnbiased (T2_fid_baseline E) {π | Admissible π} := by
  intro π hp i
  have : IsProbabilityMeasure (E.law π) := hD.law_probability π hp
  have hdesign : Measurable (fun ω => ((fun j => E.X j ω), (fun j => E.T π j ω))) :=
    (Measurable.of_eval fun j => (hD.measurable_units π hp j).1).prodMk
      (Measurable.of_eval fun j => (hD.measurable_units π hp j).2.2.2)
  have hG : E.vectorSigma π ≤ ‹MeasurableSpace Ω› := hdesign.comap_le
  have hX : Measurable[E.vectorSigma π] (E.X i) :=
    ((measurable_pi_apply i).comp measurable_fst).comp
      (comap_measurable (fun ω => ((fun j => E.X j ω), (fun j => E.T π j ω))))
  have hm : Measurable[E.vectorSigma π] (fun ω => E.μ0 (E.X i ω)) :=
    hD.means_measurable.1.comp hX
  have hi : Integrable (fun ω => E.μ0 (E.X i ω)) (E.law π) :=
    ((hD.covariate_law π hp i).comp hD.means_measurable.1).integrable_iff.mpr
      hD.means_integrable.1
  change (E.law π)[(fun ω => E.μ0 (E.X i ω)) | E.vectorSigma π]
    =ᵐ[E.law π] (fun ω => E.μ0 (E.X i ω))
  rw [condExp_of_stronglyMeasurable hG hm.stronglyMeasurable hi]

theorem T2_corrected_average_split {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C] {n : ℕ}
    (E : Experiment Ω C n) (hD : T2_OutcomeStanding E) :
    ((∀ π, Admissible π →
      (E.law π {ω | treatedCount (fun i => E.T π i ω) = 0}).toReal =
        (1 - E.q π)^n ∧
      (E.law π {ω | 0 < treatedCount (fun i => E.T π i ω)}).toReal =
        1 - (1 - E.q π)^n ∧
      E.expectedATO π = E.averageObjective E.μ1 π ∧
      E.averageObjective E.μ1 π =
        (if 0 < E.q π then
          (1 - (1 - E.q π)^n) * (E.A E.μ1 π / E.q π) else 0) ∧
      (0 < E.q π →
        eventMean (E.law π) {ω | 0 < treatedCount (fun i => E.T π i ω)}
          (fun ω => wATO (fun i => E.T π i ω) (E.observed π ω)) =
            E.A E.μ1 π / E.q π)) ∧
      (∀ π, IsBest {π | Admissible π} E.expectedATO π ↔
        IsBest {π | Admissible π} (E.averageObjective E.μ1) π)) ∧
    (Standing E → VectorUnbiased E {π | Admissible π} →
      (∀ π, Admissible π →
        E.expectedATT π = E.averageObjective E.τ π ∧
        E.averageObjective E.τ π =
          (if 0 < E.q π then
            (1 - (1 - E.q π)^n) * (E.A E.τ π / E.q π) else 0) ∧
        (0 < E.q π →
          eventMean (E.law π) {ω | 0 < treatedCount (fun i => E.T π i ω)}
            (fun ω => wATT (E.μhat π ω) (fun i => E.X i ω)
              (fun i => E.T π i ω) (E.observed π ω)) =
                E.A E.τ π / E.q π)) ∧
      (∀ π, IsBest {π | Admissible π} E.expectedATT π ↔
        IsBest {π | Admissible π} (E.averageObjective E.τ) π)) := by
  have hbase := T2_corrected_average_proof (T2_fid_baseline E)
    (T2_fid_baseline_standing E hD) (T2_fid_baseline_vectorUnbiased E hD)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro π hp
    have hπ := hbase.1 π hp
    have : IsProbabilityMeasure (E.law π) := hD.law_probability π hp
    exact ⟨hπ.1,
      T2_nonempty_mass (E.law π) (E.T π)
        (fun i => (hD.measurable_units π hp i).2.2.2) (E.q π) hπ.1,
      hπ.2.1, hπ.2.2.2.1, fun hq => (hπ.2.2.2.2.2 hq).1⟩
  · intro π
    exact (hbase.2 π).1
  · intro hS hU
    have hfull := T2_corrected_average_proof E hS hU
    refine ⟨?_, ?_⟩
    · intro π hp
      have hπ := hfull.1 π hp
      exact ⟨hπ.2.2.1, hπ.2.2.2.2.1, fun hq => (hπ.2.2.2.2.2 hq).2⟩
    · intro π
      exact (hfull.2 π).2

end
end AronowAudit.P006.Wave1
