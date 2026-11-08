import Mathlib
import SAP.P017.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace SAP.P017

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

noncomputable section

/-- Definition 2, PDF p. 2: the actual error relative to the clipped target.
The extended radius uses the identity target at infinity. -/
def ClippingErrorW3 {Ξ : Type v} (hat : ℕ → Ξ → ℝ)
    (μ : ℝ) (c : ℝ≥0∞) (n : ℕ) (ω : Ξ) : ℝ :=
  hat n ω - clipTarget μ c (hat n ω)

/-- Proof of Proposition 3, PDF p. 2, corrected, parts (a) and (d).
The exact zero region, exceedance-event inclusion and probability bound hold
at every positive sample size. Infinite radius gives the identity target and
zero actual error, including after root-n scaling, on every realization. -/
def ClippingFactsW3 {Ξ : Type v} [MeasurableSpace Ξ]
    (P : Measure Ξ) (hat : ℕ → Ξ → ℝ) (μ : ℝ) (c : ℝ≥0∞) : Prop :=
  (∀ n, 1 ≤ n → ∀ ω,
    ClippingErrorW3 hat μ c n ω = 0 ↔ inside μ c (hat n ω)) ∧
  (∀ n, 1 ≤ n → ∀ η a : ℝ, 0 < η → 0 < a →
    {ω | |ClippingErrorW3 hat μ c n ω| > η * a} ⊆
      {ω | ¬ inside μ c (hat n ω)} ∧
    pr P {ω | |ClippingErrorW3 hat μ c n ω| > η * a} ≤
      pr P {ω | ¬ inside μ c (hat n ω)}) ∧
  (c = ⊤ → ∀ n, 1 ≤ n → ∀ ω,
    clipTarget μ c (hat n ω) = hat n ω ∧
    ClippingErrorW3 hat μ c n ω = 0 ∧
    sqrtN n * ClippingErrorW3 hat μ c n ω = 0)

/-- Proof of Proposition 3, PDF p. 2, corrected, the consistency-only limits.
All fixed positive-radius tail probabilities, including the clipping-failure
probability, tend to zero. The actual clipping error is o_p(a_n) for every
deterministic scale positive at n ≥ 1; its root-n scaling is o_p(1).
The value of a scale at zero is unrestricted. -/
def ClippingLimitsW3 {Ξ : Type v} [MeasurableSpace Ξ]
    (P : Measure Ξ) (hat : ℕ → Ξ → ℝ) (μ : ℝ) (c : ℝ≥0∞) : Prop :=
  Consistent P hat μ ∧
  Tendsto (fun n => pr P {ω | ¬ inside μ c (hat n ω)}) atTop (𝓝 0) ∧
  (∀ a : ℕ → ℝ, (∀ n, 1 ≤ n → 0 < a n) →
    LittleOp P (ClippingErrorW3 hat μ c) a) ∧
  LittleOp P (fun n ω => sqrtN n * ClippingErrorW3 hat μ c n ω) (fun _ => 1)

/-- P017-T7; proof of Proposition 3, PDF p. 2, corrected on 2026-11-04.
With the finite population mean and positive, possibly infinite effect radius
of Assumption 1, the actual clipping error has its exact zero region and
exceedance-event inclusion and probability bound at every positive sample size.
Consistency alone gives every fixed-radius tail limit, the clipping-failure
probability limit, o_p(a_n) actual error for every deterministic sequence
positive at n ≥ 1, and root-n actual error o_p(1). Definition 1 additionally
gives root-n boundedness in probability and consistency, hence all these limits.
At infinite radius the target is the estimate and both the actual error and its
root-n scaling are identically zero. The clipping-event deduction requires no
normal decomposition or rate for the clipping-failure probability.
The usual measure-theoretic conditions are assumed. -/
def T7WholeStatement_W3 : Prop :=
  ∀ {Ω : Type u} {Ξ : Type v} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ),
    Measurable τ → Integrable τ G → 0 < effectRadius G τ →
    ∀ (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ),
    (∀ n, 1 ≤ n → Measurable (hat n)) →
    let μ := populationMean G τ
    let c := effectRadius G τ
    ClippingFactsW3 P hat μ c ∧
    (Consistent P hat μ → ClippingLimitsW3 P hat μ c) ∧
    (RootNNormal P hat μ →
      BoundedInProbability P (fun n ω => sqrtN n * (hat n ω - μ)) ∧
      ClippingLimitsW3 P hat μ c)

end
end SAP.P017
