import Mathlib
import SAP.P006a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

universe u v
namespace SAP.P006a
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/- The estimator assumptions are separate from the outcome and randomization design. -/
structure Standing {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) : Prop where
  px_probability : IsProbabilityMeasure E.PX
  means_measurable : Measurable E.μ0 ∧ Measurable E.μ1
  means_integrable : Integrable E.μ0 E.PX ∧ Integrable E.μ1 E.PX
  law_probability : ∀ π, Admissible π → IsProbabilityMeasure (E.law π)
  measurable_units : ∀ π, Admissible π → ∀ i,
    Measurable (E.X i) ∧ Measurable (E.Y0 i) ∧ Measurable (E.Y1 i) ∧
    Measurable (E.T π i)
  integrable_units : ∀ π, Admissible π → ∀ i,
    Integrable (E.Y0 i) (E.law π) ∧ Integrable (E.Y1 i) (E.law π) ∧
    Integrable (fun ω => E.μhat π ω (E.X i ω)) (E.law π)
  covariate_law : ∀ π, Admissible π → ∀ i,
    IdentDistrib (E.X i) (fun x : C => x) (E.law π) E.PX
  potential_law_fixed : ∀ π π', Admissible π → Admissible π' → ∀ i,
    IdentDistrib (fun ω => (E.X i ω,E.Y0 i ω,E.Y1 i ω))
      (fun ω => (E.X i ω,E.Y0 i ω,E.Y1 i ω)) (E.law π) (E.law π')
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

def PointwiseUnbiased {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (PiSet : Set (C → ℝ)) : Prop :=
  ∀ π ∈ PiSet, ∀ x, Integrable (fun ω => E.μhat π ω x) (E.law π) ∧
    (∫ ω, E.μhat π ω x ∂E.law π) = E.μ0 x

def TreatedUnbiased {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (baseline : C → ℝ) (PiSet : Set (C → ℝ)) : Prop :=
  ∀ π ∈ PiSet, ∀ i,
    (E.law π)[(fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - baseline (E.X i ω))) | E.covariateSigma i]
      =ᵐ[E.law π] (fun _ => (0 : ℝ))

def VectorUnbiased {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (PiSet : Set (C → ℝ)) : Prop :=
  ∀ π ∈ PiSet, ∀ i,
    (E.law π)[(fun ω => E.μhat π ω (E.X i ω)) | E.vectorSigma π]
      =ᵐ[E.law π] (fun ω => E.μ0 (E.X i ω))

def IndependentEstimator {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (PiSet : Set (C → ℝ)) : Prop :=
  ∃ (A : Type) (mA : MeasurableSpace A),
    letI : MeasurableSpace A := mA
    ∃ (Z : Ω → A) (f : (C → ℝ) → A → C → ℝ),
      Measurable Z ∧
      ∀ π ∈ PiSet, Measurable (fun z : A × C => f π z.1 z.2) ∧
        (∀ ω x, E.μhat π ω x = f π (Z ω) x) ∧
        IndepFun Z (fun ω => ((fun i => E.X i ω), (fun i => E.T π i ω))) (E.law π)

def MarginalBaseline {Ω X U : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] {n : ℕ}
    (E : Experiment Ω (X × U) n) (b0 : X → ℝ) : Prop :=
  Measurable b0 ∧ Integrable (fun c => b0 c.1) E.PX ∧
    ∀ π, Admissible π → ∀ i,
      (E.law π)[(fun ω => E.μ0 (E.X i ω)) |
        MeasurableSpace.comap (fun ω => (E.X i ω).1) inferInstance]
        =ᵐ[E.law π] (fun ω => b0 (E.X i ω).1)

def EstimatorUsesOnlyX {Ω X U : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] {n : ℕ}
    (E : Experiment Ω (X × U) n) : Prop :=
  ∀ π ω x u u', E.μhat π ω (x,u) = E.μhat π ω (x,u')

def marginalHeterogeneity {Ω X U : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] {n : ℕ}
    (E : Experiment Ω (X × U) n) (b0 : X → ℝ) : ℝ :=
  ∫ c, |b0 c.1-E.μ0 c| ∂E.PX

def normalizedTT {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  E.expectedTT π / n

structure OutcomeStanding {Ω C : Type*} [MeasurableSpace Ω]
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

structure PolicyDesign {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (π : C → ℝ) : Prop where
  px_probability : IsProbabilityMeasure E.PX
  means_measurable : Measurable E.μ0 ∧ Measurable E.μ1
  means_integrable : Integrable E.μ0 E.PX ∧ Integrable E.μ1 E.PX
  law_probability : IsProbabilityMeasure (E.law π)
  measurable_units : ∀ i,
    Measurable (E.X i) ∧ Measurable (E.Y0 i) ∧ Measurable (E.Y1 i) ∧
    Measurable (E.T π i)
  integrable_units : ∀ i,
    Integrable (E.Y0 i) (E.law π) ∧ Integrable (E.Y1 i) (E.law π)
  covariate_law : ∀ i,
    IdentDistrib (E.X i) (fun x : C => x) (E.law π) E.PX
  conditional_means : ∀ i,
    (E.law π)[E.Y0 i | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => E.μ0 (E.X i ω)) ∧
    (E.law π)[E.Y1 i | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => E.μ1 (E.X i ω))
  bernoulli : ∀ i,
    (E.law π)[(fun ω => bit (E.T π i ω)) | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => π (E.X i ω))
  ignorability : ∀ i (B : Set (ℝ × ℝ)), MeasurableSet B →
    (E.law π)[(fun ω => bit (E.T π i ω) *
      B.indicator (fun _ => (1 : ℝ)) (E.Y0 i ω, E.Y1 i ω)) | E.covariateSigma i]
      =ᵐ[E.law π] (fun ω => π (E.X i ω) *
        (E.law π)[(fun η => B.indicator (fun _ => (1 : ℝ))
          (E.Y0 i η, E.Y1 i η)) | E.covariateSigma i] ω)

end
end SAP.P006a
