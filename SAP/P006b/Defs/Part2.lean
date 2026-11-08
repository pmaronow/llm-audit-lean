import Mathlib
import SAP.P006b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

structure Experiment (Ω C : Type*) [MeasurableSpace Ω] [MeasurableSpace C]
    (n : ℕ) where
  
  hn : 0 < n
  
  PX : Measure C
  
  μ0 : C → ℝ
  
  μ1 : C → ℝ
  
  law : (C → ℝ) → Measure Ω
  
  X : Fin n → Ω → C
  
  Y0 : Fin n → Ω → ℝ
  
  Y1 : Fin n → Ω → ℝ
  
  T : (C → ℝ) → Fin n → Ω → Bool
  
  μhat : (C → ℝ) → Ω → C → ℝ

namespace Experiment

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}

def τ (E : Experiment Ω C n) : C → ℝ := fun x => E.μ1 x - E.μ0 x

def observed (E : Experiment Ω C n) (π : C → ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => if E.T π i ω then E.Y1 i ω else E.Y0 i ω

def V (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  ∫ ω, E.observed π ω ⟨0, E.hn⟩ - E.Y0 ⟨0, E.hn⟩ ω ∂E.law π

def meanWelfare (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  ∫ x, π x * E.τ x ∂E.PX

def expectedATO (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  ∫ ω, wATO (fun i => E.T π i ω) (E.observed π ω) ∂E.law π

def expectedATT (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  ∫ ω, wATT (E.μhat π ω) (fun i => E.X i ω)
    (fun i => E.T π i ω) (E.observed π ω) ∂E.law π

def expectedWeightedTT (E : Experiment Ω C n) (g π : C → ℝ) : ℝ :=
  ∫ ω, wWeightedTT (E.μhat π ω) g (fun i => E.X i ω)
    (fun i => E.T π i ω) (E.observed π ω) ∂E.law π

def expectedTT (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  E.expectedWeightedTT (fun _ => 1) π

def covariateSigma (E : Experiment Ω C n) (i : Fin n) : MeasurableSpace Ω :=
  MeasurableSpace.comap (E.X i) inferInstance

end Experiment

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

def normalizedTT {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  E.expectedTT π / n

end
end SAP.P006b
