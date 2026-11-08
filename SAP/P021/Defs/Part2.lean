import Mathlib
import SAP.P021.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P021

open MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section

variable {B : ℝ} {K : ℕ}

/-- Integration of a test function against a finite population's empirical law. -/
def empiricalAverage {N : ℕ} (z : Fin N → RDSState B K)
    (g : RDSState B K → ℝ) : ℝ := (∑ j, g (z j)) / (N : ℝ)

/-- The sample consists of population units whose sample mark is true. -/
def sampleSet {N : ℕ} (z : Fin N → RDSState B K) : Finset (Fin N) :=
  Finset.univ.filter fun j => (z j).2.2 = true

/-- Equation (1), extended by zero on an empty sample.
The T2 consistency statement allows empty samples at finite stages. -/
def vhEstimator {N : ℕ} (z : Fin N → RDSState B K) : ℝ :=
  (∑ j ∈ sampleSet z, outcome (z j) / degreeValue (z j).2.1) /
    (∑ j ∈ sampleSet z, 1 / degreeValue (z j).2.1)

/-- Weak convergence in probability of the realized joint empirical laws.
Every continuous real function on this common compact state space is bounded. -/
def EmpiricalWeakInProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Measure (RDSState B K)) (N : ℕ → ℕ)
    (z : (r : ℕ) → Ω → Fin (N r) → RDSState B K) : Prop :=
  ∀ g : RDSState B K → ℝ, Continuous g →
    TendstoInMeasure P (fun r ω => empiricalAverage (z r ω) g) atTop
      (fun _ => ∫ x, g x ∂F)

/-- Proposition 1, including the equalities in its printed proof.
All sums use positive-mass degree strata under the standing null-event convention. -/
def T1Statement : Prop :=
  ∀ (B : ℝ) (K : ℕ) (F : Measure (RDSState B K)), IsProbabilityMeasure F →
  ∀ (c : ℝ) (f : Fin K → ℝ), Ignorability F → KnownSampling F c f →
    0 < sampleFraction F ∧ degreeSupport F = observedSupport F ∧ c ≠ 0 ∧
    (∀ k ∈ degreeSupport F,
      0 < sampledMass F k ∧ 0 < c * f k ∧ f k ≠ 0 ∧
      degreeMass F k = observedDegreeMass F k * sampleFraction F /
        samplingProbability F k ∧
      degreeMass F k = (sampleFraction F / c) * (observedDegreeMass F k / f k)) ∧
    (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k) = c / sampleFraction F ∧
    (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k) ≠ 0 ∧
    populationMean F =
      (∑ k ∈ degreeSupport F, sampledMean F k * (observedDegreeMass F k / f k)) /
        (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k) ∧
    populationMean F =
      (∑ k ∈ degreeSupport F,
        degreeMean F k * (sampleFraction F / c) * (observedDegreeMass F k / f k)) /
        (∑ k ∈ degreeSupport F,
          (sampleFraction F / c) * (observedDegreeMass F k / f k)) ∧
    (∑ k ∈ degreeSupport F,
        degreeMean F k * (sampleFraction F / c) * (observedDegreeMass F k / f k)) /
        (∑ k ∈ degreeSupport F,
          (sampleFraction F / c) * (observedDegreeMass F k / f k)) =
      (∑ k ∈ degreeSupport F, degreeMean F k * (observedDegreeMass F k / f k)) /
        (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k)

/-- The random and deterministic consistency conclusions, with a nonempty-sample guard. -/
def T2Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  (∀ (B : ℝ) (K : ℕ) (P : Measure Ω), IsProbabilityMeasure P →
    0 ≤ B → 0 < K →
    ∀ F : Measure (RDSState B K), IsProbabilityMeasure F →
    ∀ (N : ℕ → ℕ), (∀ r, 0 < N r) →
    ∀ z : (r : ℕ) → Ω → Fin (N r) → RDSState B K,
    (∀ r j, Measurable (fun ω => z r ω j)) →
    (∀ r, ∀ᵐ ω ∂P, (sampleSet (z r ω)).Nonempty) →
    EmpiricalWeakInProbability P F N z →
    ∀ (c a : ℝ), a ≠ 0 → Ignorability F →
    KnownSampling F c (fun k => a * degreeValue k) →
    TendstoInMeasure P (fun r ω => vhEstimator (z r ω)) atTop
      (fun _ => populationMean F)) ∧
  (∀ (B : ℝ) (K : ℕ), 0 ≤ B → 0 < K →
    ∀ F : Measure (RDSState B K), IsProbabilityMeasure F →
    ∀ (N : ℕ → ℕ), (∀ r, 0 < N r) →
    ∀ z : (r : ℕ) → Fin (N r) → RDSState B K,
    (∀ r, (sampleSet (z r)).Nonempty) →
    (∀ g : RDSState B K → ℝ, Continuous g →
      Tendsto (fun r => empiricalAverage (z r) g) atTop (𝓝 (∫ x, g x ∂F))) →
    ∀ (c a : ℝ), a ≠ 0 → Ignorability F →
    KnownSampling F c (fun k => a * degreeValue k) →
    Tendsto (fun r => vhEstimator (z r)) atTop (𝓝 (populationMean F)))

end
end SAP.P021
