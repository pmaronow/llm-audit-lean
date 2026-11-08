import Mathlib
import SAP.P047.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P047

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

/-- Finite-sample assertions for the ATE interval and the one-mean interval. -/
def T1Statement : Prop :=
  (∀ (L : CausalLaw) (B ε : ℝ), BoundedOverlap L B ε →
    (L.measure[score L | covariateSigma] =ᵐ[L.measure]
      L.measure[fun u => potential true u - potential false u | covariateSigma]) ∧
    ((∫ u, score L u ∂L.measure) = ate L) ∧
    (∀ᵐ u ∂L.measure, |score L u| ≤ B / ε) ∧
    (∀ n : ℕ, 1 ≤ n →
      ((∫ s, estimator L n s ∂sampleLaw L.measure) = ate L) ∧
      (∀ t : ℝ, 0 ≤ t → (sampleLaw L.measure).real
        {s | t ≤ |estimator L n s - ate L|} ≤
          2 * Real.exp (-(n : ℝ) * t ^ 2 * ε ^ 2 / (2 * B ^ 2))) ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        (1 - α ≤ (sampleLaw L.measure).real
          {s | ate L ∈ confidenceInterval L B ε α n s}) ∧
        (0 ≤ halfWidth B ε α n) ∧
        (∀ s : ℕ → UnitData,
          intervalWidth L B ε α n s = 2 * halfWidth B ε α n ∧
          intervalWidth L B ε α n s =
            (2 * B / ε * Real.sqrt (2 * Real.log (2 / α))) / Real.sqrt n) ∧
        (Real.sqrt n * (2 * halfWidth B ε α n) =
          2 * B / ε * Real.sqrt (2 * Real.log (2 / α)))))) ∧
  (∀ (L : CausalLaw) (ε : ℝ), TreatedMeanModel L ε →
    (∀ᵐ u ∂L.measure, treatedScore L u ∈ Set.Icc 0 (1 / ε)) ∧
    (∀ n : ℕ, 1 ≤ n →
      ((∫ s, treatedEstimator L n s ∂sampleLaw L.measure) = treatedMean L) ∧
      (∀ t : ℝ, 0 ≤ t → (sampleLaw L.measure).real
        {s | t ≤ |treatedEstimator L n s - treatedMean L|} ≤
          2 * Real.exp (-2 * n * ε ^ 2 * t ^ 2)) ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        1 - α ≤ (sampleLaw L.measure).real
          {s | treatedMean L ∈ Set.Icc
            (treatedEstimator L n s - treatedHalfWidth ε α n)
            (treatedEstimator L n s + treatedHalfWidth ε α n)})))

/-- Supremum over every positive sample size and every population with the
same B and ε. The inserted zero fixes the empty-set convention. -/
def knownRootRisk (B ε K : ℝ) : ℝ :=
  sSup (insert 0 {r | ∃ L : CausalLaw, BoundedOverlap L B ε ∧
    ∃ n : ℕ, 1 ≤ n ∧ r = (sampleLaw L.measure).real
      {s | K < Real.sqrt n * |estimator L n s - ate L|}})

/-- Uniform tightness with an exact tail bound and a fixed-law normal limit.
The normal distribution includes the point mass at zero. -/
def T2Statement : Prop :=
  ∀ B ε : ℝ, 0 < B → 0 < ε → ε ≤ 1 / 2 →
    Tendsto (knownRootRisk B ε) atTop (𝓝 0) ∧
    (∀ L : CausalLaw, BoundedOverlap L B ε →
      (∀ n : ℕ, 1 ≤ n → ∀ K : ℝ, 0 ≤ K →
        (sampleLaw L.measure).real
          {s | K ≤ Real.sqrt n * |estimator L n s - ate L|} ≤
            2 * Real.exp (-K ^ 2 * ε ^ 2 / (2 * B ^ 2))) ∧
      variance (score L) L.measure ≤ B ^ 2 / ε ^ 2 ∧
      TendstoInDistribution (fun (n : ℕ) s => Real.sqrt n * (estimator L n s - ate L))
        atTop id (fun _ => sampleLaw L.measure)
        (gaussianReal 0 (variance (score L) L.measure).toNNReal))

end

end SAP.P047
