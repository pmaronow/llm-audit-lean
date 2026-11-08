import Mathlib
import SAP.P021.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P021

open MeasureTheory Filter Topology

/-- P021-T2; Corollary 1, p. 101 (PDF p. 2), and Eq. (1), p. 100 (PDF p. 1).
Under the common bounded support and weak convergence of the realized joint empirical
laws, mean ignorability and sampling probabilities proportional to degree imply that
the VH estimator converges to the population outcome mean, in probability for random
populations and ordinarily for deterministic populations. The sample consists of the
units marked S = 1. Equation (1) is assigned zero on an empty sample; finite stages may
have empty samples. -/
def T2WholeStatement : Prop :=
  (∀ (Ω : Type*) [MeasurableSpace Ω],
    ∀ (B : ℝ) (K : ℕ) (P : Measure Ω), IsProbabilityMeasure P →
    0 ≤ B → 0 < K →
    ∀ F : Measure (RDSState B K), IsProbabilityMeasure F →
    ∀ (N : ℕ → ℕ), (∀ r, 0 < N r) →
    ∀ z : (r : ℕ) → Ω → Fin (N r) → RDSState B K,
    (∀ r j, Measurable (fun ω => z r ω j)) →
    EmpiricalWeakInProbability P F N z →
    ∀ (c a : ℝ), a ≠ 0 → Ignorability F →
    KnownSampling F c (fun k => a * degreeValue k) →
    TendstoInMeasure P (fun r ω => vhEstimator (z r ω)) atTop
      (fun _ => populationMean F)) ∧
  (∀ (B : ℝ) (K : ℕ), 0 ≤ B → 0 < K →
    ∀ F : Measure (RDSState B K), IsProbabilityMeasure F →
    ∀ (N : ℕ → ℕ), (∀ r, 0 < N r) →
    ∀ z : (r : ℕ) → Fin (N r) → RDSState B K,
    (∀ g : RDSState B K → ℝ, Continuous g →
      Tendsto (fun r => empiricalAverage (z r) g) atTop (𝓝 (∫ x, g x ∂F))) →
    ∀ (c a : ℝ), a ≠ 0 → Ignorability F →
    KnownSampling F c (fun k => a * degreeValue k) →
    Tendsto (fun r => vhEstimator (z r)) atTop (𝓝 (populationMean F)))

end SAP.P021
