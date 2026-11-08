import Mathlib
import SAP.P027b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The conditional sampling variance for one generated population, on the mean scale. -/
def wholeStrataV {Ξ : Type} {M : ℕ} (hM : 2 ≤ M) (α : ℝ)
    (ε : (Fin M × Fin 2) → Ξ → ℝ) (ξ : Ξ) : ℝ :=
  let D := strataDesign M (by omega)
  variance D (htMean D (stratumOutcomes α ε ξ))

/-- The sampling expectation of the HT variance estimate, divided by N squared. -/
def wholeStrataH {Ξ : Type} {M : ℕ} (hM : 2 ≤ M) (α : ℝ)
    (ε : (Fin M × Fin 2) → Ξ → ℝ) (ξ : Ξ) : ℝ :=
  let D := strataDesign M (by omega)
  expect D (fun ω => htVarianceEstimator D (stratumOutcomes α ε ξ) ω / (2*(M:ℝ))^2)

/-- The sampling expectation of the quadratic corrected estimate, on the mean scale. -/
def wholeStrataC {Ξ : Type} {M : ℕ} (hM : 2 ≤ M) (α : ℝ)
    (ε : (Fin M × Fin 2) → Ξ → ℝ) (ξ : Ξ) : ℝ :=
  let D := strataDesign M (by omega)
  expect D (fun ω => c2Estimator D (stratumOutcomes α ε ξ) ω / (2*(M:ℝ))^2)

/-- The sampling expectation of the collapsed-stratum estimate. -/
def wholeStrataCS {Ξ : Type} {M : ℕ} (hM : 2 ≤ M) (α : ℝ)
    (ε : (Fin M × Fin 2) → Ξ → ℝ) (ξ : Ξ) : ℝ :=
  expect (strataDesign M (by omega)) (collapsedEstimator (stratumOutcomes α ε ξ))

/-- Existence of all outcome expectations used in the two numerical witnesses. -/
def WholeStrataIntegrable {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    {M : ℕ} (hM : 2 ≤ M) (α : ℝ) (ε : (Fin M × Fin 2) → Ξ → ℝ) : Prop :=
  Integrable (wholeStrataV hM α ε) μ ∧
  Integrable (wholeStrataH hM α ε) μ ∧
  Integrable (wholeStrataC hM α ε) μ ∧
  Integrable (wholeStrataCS hM α ε) μ ∧
  Integrable (fun ξ => wholeStrataC hM α ε ξ - wholeStrataV hM α ε ξ) μ ∧
  Integrable (fun ξ => wholeStrataCS hM α ε ξ - wholeStrataV hM α ε ξ) μ

/-- P027-T14; supplement Section B, p. A2 and Table A1, p. A5.
At M=5 the two fixed populations have the stated true variances, all three expected
estimates, biases, and reversed bias rankings. Independent standard Gaussian errors
give the model-averaged biases 2/5 versus 1/10 at alpha=0 and 18/5 versus 41/10 at
alpha=2, again reversing the ranking. At M=500 and alpha=0 the model averages of the
conditional sampling variance, corrected estimate, and collapsed estimate are
499/1000, 499/500, and 1/2, with relative biases 1 and 1/499. All outcome expectations
exist and the relative-bias denominator is positive. The rounded simulation rows
are comparison context, rather than additional exact expectation identities. -/
def T14WholeStatement : Prop :=
  T14Statement ∧
  Fintype.card (Fin 5 × Fin 5) = 25 ∧
  (∀ ω, (strataDesign 5 (by norm_num)).weight ω = 1/25) ∧
  (∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
      (ε : (Fin 5 × Fin 2) → Ξ → ℝ), GaussianNoise μ ε 1 →
    WholeStrataIntegrable μ (by norm_num : 2 ≤ 5) 0 ε ∧
    WholeStrataIntegrable μ (by norm_num : 2 ≤ 5) 2 ε ∧
    let BC := fun α => outcomeE μ (fun ξ =>
      wholeStrataC (by norm_num : 2 ≤ 5) α ε ξ - wholeStrataV (by norm_num) α ε ξ)
    let BS := fun α => outcomeE μ (fun ξ =>
      wholeStrataCS (by norm_num : 2 ≤ 5) α ε ξ - wholeStrataV (by norm_num) α ε ξ)
    BC 0 = 2/5 ∧ BS 0 = 1/10 ∧ BS 0 < BC 0 ∧
    BC 2 = 18/5 ∧ BS 2 = 41/10 ∧ BC 2 < BS 2) ∧
  (∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
      (ε : (Fin 500 × Fin 2) → Ξ → ℝ), GaussianNoise μ ε 1 →
    WholeStrataIntegrable μ (by norm_num : 2 ≤ 500) 0 ε ∧
    let V := outcomeE μ (wholeStrataV (by norm_num : 2 ≤ 500) 0 ε)
    let C := outcomeE μ (wholeStrataC (by norm_num : 2 ≤ 500) 0 ε)
    let CS := outcomeE μ (wholeStrataCS (by norm_num : 2 ≤ 500) 0 ε)
    V = 499/1000 ∧ C = 499/500 ∧ CS = 1/2 ∧ 0 < V ∧
    (C-V)/V = 1 ∧ (CS-V)/V = 1/499)

/-- Equal mixing weights for the two fixed stratum means. -/
def wholeFairSignLaw : Measure ℝ :=
  bernoulliMeasure 1 (-1) ⟨1/2, by constructor <;> norm_num⟩

/-- Coordinate 0 is the common stratum sign; coordinates 1 and 2 are the distinct
units' independent standard Gaussian errors. Joint independence is needed for
the conditional-on-stratum assertion, not just for the unconditional moments. -/
def WholeGaussianPair {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (X : Fin 3 → Ξ → ℝ) : Prop :=
  (∀ i, Measurable (X i)) ∧
  μ.map (X 0) = wholeFairSignLaw ∧
  μ.map (X 1) = gaussianReal 0 1 ∧
  μ.map (X 2) = gaussianReal 0 1 ∧
  iIndepFun X μ

/-- The two units share the same random stratum, at the witness alpha=1/2. -/
def wholePairY {Ξ : Type} (X : Fin 3 → Ξ → ℝ) (ξ : Ξ) : ℝ :=
  (1/2:ℝ)*X 0 ξ + X 1 ξ

/-- The second unit has its own error and the same stratum sign. -/
def wholePairY' {Ξ : Type} (X : Fin 3 → Ξ → ℝ) (ξ : Ξ) : ℝ :=
  (1/2:ℝ)*X 0 ξ + X 2 ξ

/-- Ordinary Pearson correlation; the conclusions below establish positive variances. -/
def wholePearson {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (Y Y' : Ξ → ℝ) : ℝ :=
  ProbabilityTheory.covariance Y Y' μ /
    Real.sqrt (ProbabilityTheory.variance Y μ * ProbabilityTheory.variance Y' μ)

/-- Divisor-2 variance of the two fixed means, contrasted with stratumMeansVariance. -/
def wholeMeansPopulationVariance (α : ℝ) : ℝ :=
  (∑ s : Fin 2, (stratumMeans α s - (∑ t : Fin 2, stratumMeans α t)/2)^2)/2

/-- P027-T16; supplement Section B, p. A2, with labels on pp. A5–A6.
For an equally likely common stratum and independent standard Gaussian errors,
alpha=1/2 gives zero outcome means, variances 5/4, covariance 1/4, and Pearson
correlation 1/5. The printed ratio is 1/3 and exceeds that correlation by 2/15.
The two fixed means average to zero; their divisor-1 variance is 1/2, giving the
printed variance ratio, while their divisor-2 variance is 1/4, equal to the variance
of the random stratum effect. Conditional on either stratum the outcome variances
are one and their covariance and correlation are zero. All variables used in
these correlations have finite second moments, and each conditioning event has
probability 1/2. This compares the printed parameter with ordinary Pearson
correlation and does not identify the authors' intended convention. -/
def T16WholeStatement : Prop :=
  ((∑ s : Fin 2, stratumMeans (1/2) s)/2 = 0 ∧
    stratumMeansVariance (1/2) = 1/2 ∧
    heterogeneity (1/2) = stratumMeansVariance (1/2)/(stratumMeansVariance (1/2)+1) ∧
    wholeMeansPopulationVariance (1/2) = 1/4) ∧
  ∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
      (X : Fin 3 → Ξ → ℝ), WholeGaussianPair μ X →
    PairMoments μ (X 0) (X 1) (X 2) ∧
    (∀ i, MemLp (X i) 2 μ) ∧
    MemLp (wholePairY X) 2 μ ∧ MemLp (wholePairY' X) 2 μ ∧
    outcomeE μ (wholePairY X) = 0 ∧ outcomeE μ (wholePairY' X) = 0 ∧
    ProbabilityTheory.variance (wholePairY X) μ = 5/4 ∧
    ProbabilityTheory.variance (wholePairY' X) μ = 5/4 ∧
    ProbabilityTheory.covariance (wholePairY X) (wholePairY' X) μ = 1/4 ∧
    wholePearson μ (wholePairY X) (wholePairY' X) = 1/5 ∧
    heterogeneity (1/2) = 1/3 ∧
    heterogeneity (1/2) - wholePearson μ (wholePairY X) (wholePairY' X) = 2/15 ∧
    wholePearson μ (wholePairY X) (wholePairY' X) ≠ heterogeneity (1/2) ∧
    ProbabilityTheory.variance (fun ξ => (1/2:ℝ)*X 0 ξ) μ =
      wholeMeansPopulationVariance (1/2) ∧
    (∀ s : ℝ, s = 1 ∨ s = -1 →
      μ {ξ | X 0 ξ = s} = 1/2 ∧
      let ν := ProbabilityTheory.cond μ {ξ | X 0 ξ = s}
      IsProbabilityMeasure ν ∧
      MemLp (wholePairY X) 2 ν ∧ MemLp (wholePairY' X) 2 ν ∧
      ProbabilityTheory.variance (wholePairY X) ν = 1 ∧
      ProbabilityTheory.variance (wholePairY' X) ν = 1 ∧
      ProbabilityTheory.covariance (wholePairY X) (wholePairY' X) ν = 0 ∧
      wholePearson ν (wholePairY X) (wholePairY' X) = 0)

end
end SAP.P027b
