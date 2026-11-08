import SAP.P036.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P036

open Finset
open scoped BigOperators

noncomputable section

/-- The row of the unadjusted design matrix, indexed by intercept and peer slope. -/
def designRow {ι : Type*} (s : Finset ι) (i : ι) (a : Fin 2) : ℝ :=
  if a = 0 then 1 else peers (s : Set ι) i

/-- Entries of the Gram matrix D'D. -/
def gram {ι : Type*} [Fintype ι] (s : Finset ι) (a b : Fin 2) : ℝ :=
  ∑ i, designRow s i a * designRow s i b

/-- The explicit inverse; T2 certifies both products with the Gram matrix. -/
def gramInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (a b : Fin 2) : ℝ :=
  if a = 0 then
    if b = 0 then 1 / (sᶜ.card : ℝ) else -1 / (sᶜ.card : ℝ)
  else
    if b = 0 then -1 / (sᶜ.card : ℝ)
    else 1 / (s.card : ℝ) + 1 / (sᶜ.card : ℝ)

/-- The entries of (D'D)⁻¹D'Y. -/
def regressionCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (Y : ι → ℝ) (a : Fin 2) : ℝ :=
  ∑ b, gramInverse s a b * ∑ i, designRow s i b * Y i

/-- Residuals from the unique least-squares coefficients of T1. -/
def olsResidual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (Y : ι → ℝ) (i : ι) : ℝ :=
  Y i - (olsCoefficients s Y).1 - (olsCoefficients s Y).2 * peers (s : Set ι) i

/-- The diagonal entry Dᵢ'(D'D)⁻¹Dᵢ of the hat matrix. -/
def leverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (i : ι) : ℝ :=
  ∑ a, ∑ b, designRow s i a * gramInverse s a b * designRow s i b

/-- The HC2 sandwich, with the finite sum over units outside the matrix-entry sums. -/
def hc2Covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (Y : ι → ℝ) (a b : Fin 2) : ℝ :=
  ∑ i, ∑ u, ∑ v, gramInverse s a u *
    ((olsResidual s Y i)^2 / (1 - leverage s i) *
      designRow s i u * designRow s i v) * gramInverse s v b

/-- The treatment-coefficient diagonal entry of the HC2 covariance. -/
def hc2Variance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  hc2Covariance s Y 1 1

/-- The Neyman sample-variance estimator. -/
def neymanEstimate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (Y : ι → ℝ) : ℝ :=
  sampleVariance s Y / (s.card : ℝ) + sampleVariance sᶜ Y / (sᶜ.card : ℝ)

/-- One arm's binary-response HC2 contribution. -/
def binaryHC2Arm (n k : ℕ) : ℝ :=
  (k : ℝ) * ((n : ℝ) - (k : ℝ)) / ((n : ℝ)^2 * ((n : ℝ) - 1))

/-- The variance calculated from response counts in the paper's two arms. -/
def tableHC2 (k₁ k₀ : ℕ) : ℝ :=
  binaryHC2Arm 94 k₁ + binaryHC2Arm 95 k₀

/-- All subsets of the finite population of the specified treatment size. -/
def assignments {ι : Type*} [Fintype ι] (n₁ : ℕ) : Finset (Finset ι) :=
  (univ : Finset ι).powersetCard n₁

/-- Uniform expectation over complete randomization, with fixed outcomes. -/
def designExpectation {ι : Type*} [Fintype ι] (n₁ : ℕ)
    (F : Finset ι → ℝ) : ℝ :=
  Finset.expect (assignments (ι := ι) n₁) F

/-- Variance under the same uniform assignment distribution. -/
def designVariance {ι : Type*} [Fintype ι] (n₁ : ℕ)
    (F : Finset ι → ℝ) : ℝ :=
  designExpectation n₁ (fun s => (F s - designExpectation n₁ F)^2)

/-- Each unit reveals the fixed potential outcome for its assigned arm. -/
def observedOutcome {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (Y₁ Y₀ : ι → ℝ) (i : ι) : ℝ :=
  if i ∈ s then Y₁ i else Y₀ i

/-- The finite-population mean. -/
def populationMean {ι : Type*} [Fintype ι] (Y : ι → ℝ) : ℝ := armMean univ Y

/-- The finite-population variance with divisor N-1. -/
def populationVariance {ι : Type*} [Fintype ι] (Y : ι → ℝ) : ℝ :=
  armSS univ Y / ((Fintype.card ι : ℝ) - 1)

/-- The individual treatment effect. -/
def unitEffect {ι : Type*} (Y₁ Y₀ : ι → ℝ) (i : ι) : ℝ := Y₁ i - Y₀ i

/-- The unadjusted OLS treatment coefficient under an assignment. -/
def estimatedEffect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y₁ Y₀ : ι → ℝ) (s : Finset ι) : ℝ :=
  (olsCoefficients s (observedOutcome s Y₁ Y₀)).2

end

end SAP.P036
