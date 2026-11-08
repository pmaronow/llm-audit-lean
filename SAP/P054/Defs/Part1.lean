import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P054

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I]

/-- Number of selected respondents, for binary membership indicators. -/
def groupCount (d : I → ℝ) : ℝ := ∑ i, d i

/-- Total survey weight among selected respondents. -/
def groupWeight (d w : I → ℝ) : ℝ := ∑ i, d i * w i

/-- Weighted binary-response ratio, used below only with positive total weight. -/
def weightedProportion (d w y : I → ℝ) : ℝ :=
  (∑ i, d i * w i * y i) / groupWeight d w

/-- Centered respondent contribution to the weighted ratio. -/
def ratioResidual (d w y : I → ℝ) (i : I) : ℝ :=
  d i * w i * (y i - weightedProportion d w y)

/-- Squared-weight component of the independent-respondent linearisation. -/
def squaredWeightTerm (d w y : I → ℝ) : ℝ :=
  (∑ i, d i * (w i)^2 * (y i - weightedProportion d w y)^2) /
    (groupWeight d w)^2

/-- Full-sample normalized squared-residual variance used in the reconstruction. -/
def linearisationVariance {N : ℕ} (d w y : Fin N → ℝ) : ℝ :=
  ((∑ i, (ratioResidual d w y i)^2) / ((N : ℝ) * ((N : ℝ) - 1))) /
    (groupWeight d w / (N : ℝ))^2

/-- The reference binary-proportion formula V0, with the same weighted ratio. -/
def referenceVariance (d w y : I → ℝ) : ℝ :=
  weightedProportion d w y * (1 - weightedProportion d w y) / groupCount d

/-- Weighted residual sum of squares for an intercept-only fit. -/
def weightedResidualSumSquares (d w y : I → ℝ) : ℝ :=
  ∑ i, d i * w i * (y i - weightedProportion d w y)^2

/-- Classical intercept-only weighted-least-squares variance formula. -/
def classicalWlsVariance (d w y : I → ℝ) : ℝ :=
  weightedResidualSumSquares d w y / ((groupCount d - 1) * groupWeight d w)

/-- The complete conditional ratio reconstruction, including its equal-weight consequence. -/
def T1Statement : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (d w y : Fin N → ℝ),
    (∀ i, d i = 0 ∨ d i = 1) →
    (∀ i, y i = 0 ∨ y i = 1) →
    (∀ i, 0 < w i) → 0 < groupCount d →
    (∑ i, ratioResidual d w y i) = 0 ∧
    linearisationVariance d w y =
      (N : ℝ) / ((N : ℝ) - 1) * squaredWeightTerm d w y ∧
    (∀ c : ℝ, 0 < c → w = (fun _ => c) →
      squaredWeightTerm d w y = referenceVariance d w y ∧
      linearisationVariance d w y =
        (N : ℝ) / ((N : ℝ) - 1) * referenceVariance d w y)

/-- The complete conditional classical weighted-least-squares reconstruction. -/
def T2Statement : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (d w y : Fin N → ℝ),
    (∀ i, d i = 0 ∨ d i = 1) →
    (∀ i, y i = 0 ∨ y i = 1) →
    (∀ i, 0 < w i) → 2 ≤ groupCount d →
    weightedResidualSumSquares d w y =
      groupWeight d w * weightedProportion d w y * (1 - weightedProportion d w y) ∧
    classicalWlsVariance d w y =
      weightedProportion d w y * (1 - weightedProportion d w y) / (groupCount d - 1) ∧
    classicalWlsVariance d w y =
      groupCount d / (groupCount d - 1) * referenceVariance d w y

end

end SAP.P054
