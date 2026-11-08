import SAP.P061b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061b
open Filter
open scoped BigOperators Classical Topology

def T16Statement : Prop :=
  ∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g y : Schedule Ω N) (d : ℝ),
  0 < N → (∀ i, 0 < exposureProbability D g i d) → ExposureMoment D g y d →
  HasFirstMoment D (htMean D g y d) ∧
  designMean D (htMean D g y d) = averageExposureMean D g y d ∧
  (∀ e : ℝ, (∀ i, 0 < exposureProbability D g i e) → ExposureMoment D g y e →
    HasFirstMoment D (htDifference D g y d e) ∧
    designMean D (htDifference D g y d e) = averageContrast D g y d e)

def T17Statement : Prop :=
  (∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g y : Schedule Ω N) (d : ℝ) (n : ℕ),
    0 < N → 0 < n → (∀ i, exposureProbability D g i d = (n : ℝ) / N) →
    ∀ z, htMean D g y d z = exposedMean g y d n z) ∧
  (∀ {N : ℕ} (D : AtomicDesign (Fin N → Fin 2)) (y : Schedule (Fin N → Fin 2) N)
      (n : ℕ), 0 < n → n < N → UniformFixedCount D n →
    (∀ i, exposureProbability D (fun j z => (z j).val) i 1 = (n : ℝ) / N ∧
      exposureProbability D (fun j z => (z j).val) i 0 = ((N - n : ℕ) : ℝ) / N) ∧
    designMean D (fun z => exposedMean (fun j w => (w j).val) y 1 n z -
      exposedMean (fun j w => (w j).val) y 0 (N - n) z) =
      averageContrast D (fun j z => (z j).val) y 1 0)

def T18Statement : Prop :=
  ∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g y : Schedule Ω N) (d e : ℝ),
  0 < N → (∀ i, 0 < exposureProbability D g i d ∧ 0 < exposureProbability D g i e) →
  SupportStable D g y →
  (∀ i z, InSupport D z →
    (if g i z = d then y i z else 0) = (if g i z = d then exposureMean D g y i d else 0)) ∧
  (∀ z, InSupport D z → htMean D g y d z =
    (N : ℝ)⁻¹ * ∑ i, (if g i z = d then exposureMean D g y i d else 0) /
      exposureProbability D g i d) ∧
  designVariance D (htMean D g y d) = indicatorVarianceSum D g y d ∧
  designVariance D (htMean D g y d) = covarianceSum D g y d d ∧
  designCovariance D (htMean D g y d) (htMean D g y e) = covarianceSum D g y d e ∧
  designVariance D (htDifference D g y d e) = designVariance D (htMean D g y d) +
    designVariance D (htMean D g y e) - 2 * designCovariance D (htMean D g y d) (htMean D g y e) ∧
  (∀ i, jointExposureProbability D g i i d d = exposureProbability D g i d) ∧
  (d ≠ e → ∀ i, jointExposureProbability D g i i d e = 0)

def T19Statement : Prop :=
  ∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g y : Schedule Ω N) (d : ℝ),
  0 < N → (∀ i, 0 < exposureProbability D g i d) → SupportStable D g y →
  ((∀ i j, 0 < jointExposureProbability D g i j d d) →
    designMean D (htVarianceEstimate D g y d) = designVariance D (htMean D g y d) ∧
    designMean D (htVarianceEstimate D g y d) = covarianceSum D g y d d) ∧
  designMean D (conservativeVarianceEstimate D g y d) ≥ designVariance D (htMean D g y d) ∧
  (∀ i j, |exposureMean D g y i d * exposureMean D g y j d| ≤
    exposureMean D g y i d ^ 2 / 2 + exposureMean D g y j d ^ 2 / 2)

def T20Statement : Prop :=
  ∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g y F : Schedule Ω N) (d : ℝ),
  0 < N → (∀ i, 0 < exposureProbability D g i d) → ExposureMoment D g y d →
  (∀ i, HasFirstMoment D (F i)) → ExposureMoment D g F d →
  (PredictionCalibrated D g F d → HasFirstMoment D (adjustedMean D g y F d) ∧
    designMean D (adjustedMean D g y F d) = averageExposureMean D g y d) ∧
  ((∀ i, EventIndependent D (exposureIndicator g i d) (F i)) →
    PredictionCalibrated D g F d ∧ HasFirstMoment D (adjustedMean D g y F d) ∧
    designMean D (adjustedMean D g y F d) = averageExposureMean D g y d) ∧
  ((∀ i, MeanIndependent D (F i) (exposureIndicator g i d)) →
    PredictionCalibrated D g F d ∧ HasFirstMoment D (adjustedMean D g y F d) ∧
    designMean D (adjustedMean D g y F d) = averageExposureMean D g y d)

/-- Limits explicitly use population sizes N + 1, so all population denominators are positive. -/
def T21Statement : Prop :=
  ∀ {Ω : ℕ → Type} (D : ∀ N, AtomicDesign (Ω N)) (g y : ∀ N, Schedule (Ω N) N)
      (d : ℝ) (b c : ℕ → ℝ),
  (∀ N, 0 ≤ b N) → (∀ N, 0 ≤ c N) →
  (∀ N i, 0 < exposureProbability (D N) (g N) i d) →
  (∀ N, SupportStable (D N) (g N) (y N)) →
  (∀ N i, eventProbability (D N) (fun z =>
    |(if g N i z = d then y N i z else 0) / exposureProbability (D N) (g N) i d| > c N) = 0) →
  (∀ N, ∑ i, ∑ j, |jointExposureProbability (D N) (g N) i j d d -
    exposureProbability (D N) (g N) i d * exposureProbability (D N) (g N) j d| = b N) →
  Tendsto (fun N => b (N + 1) / ((N + 1 : ℕ) : ℝ)^2) atTop (𝓝 0) →
  Tendsto (fun N => b (N + 1) * c (N + 1)^2 / ((N + 1 : ℕ) : ℝ)^2) atTop (𝓝 0) →
  ∀ ε : ℝ, 0 < ε → Tendsto (fun N => eventProbability (D (N + 1)) (fun z =>
    |htMean (D (N + 1)) (g (N + 1)) (y (N + 1)) d z -
      averageExposureMean (D (N + 1)) (g (N + 1)) (y (N + 1)) d| > ε))
    atTop (𝓝 0)

end SAP.P061b
