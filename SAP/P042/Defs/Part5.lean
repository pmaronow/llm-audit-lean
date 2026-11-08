import SAP.P042.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042

noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

/-- Fixed linear combinations preserve means and have the full covariance variance. -/
def LinearPoolingLaw : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ℕ) (a : Fin J → ℝ) (D : Fin J → Ω → ℝ),
    (∀ j, MemLp (D j) 2 μ) →
    (∫ ω, pooled a D ω ∂μ) = ∑ j, a j * (∫ ω, D j ω ∂μ) ∧
    variance (pooled a D) μ = covarianceForm a (fun j k => covariance (D j) (D k) μ) ∧
    covarianceForm a (fun j k => covariance (D j) (D k) μ) =
      (∑ j, a j^2 * variance (D j) μ) +
        2*offDiagonal a (fun j k => covariance (D j) (D k) μ)

/-- Precision weighting and the exact condition for the diagonal calculation. -/
def PrecisionPoolingLaw : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ℕ), 0 < J → ∀ (D : Fin J → Ω → ℝ),
    (∀ j, MemLp (D j) 2 μ) → (∀ j, 0 < variance (D j) μ) →
    let v := fun j => variance (D j) μ
    let a := normalizedWeight v
    let Sigma := fun j k => covariance (D j) (D k) μ
    0 < totalWeight v ∧ (∀ j, 0 < a j) ∧ (∑ j, a j) = 1 ∧
    diagonalVariance v = (totalWeight v)⁻¹ ∧
    variance (pooled a D) μ = (totalWeight v)⁻¹ + 2*offDiagonal a Sigma ∧
    (variance (pooled a D) μ = (totalWeight v)⁻¹ ↔ offDiagonal a Sigma = 0) ∧
    ((∀ j k, j ≠ k → Sigma j k = 0) →
      variance (pooled a D) μ = (totalWeight v)⁻¹) ∧
    ((∀ j k, j ≠ k → 0 ≤ Sigma j k) →
      (∃ j k, j < k ∧ 0 < Sigma j k) →
      (totalWeight v)⁻¹ < variance (pooled a D) μ) ∧
    (∀ z : ℝ, z * Real.sqrt (variance (pooled a D) μ) =
      z * Real.sqrt (covarianceForm a Sigma)) ∧
    (∀ z : ℝ, 0 < z →
      (z * Real.sqrt (variance (pooled a D) μ) = z * Real.sqrt ((totalWeight v)⁻¹) ↔
        offDiagonal a Sigma = 0))

/-- Uncorrelated arm means produce the shared-control covariance. -/
def SharedControlLaw : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B C : Ω → ℝ), MemLp A 2 μ → MemLp B 2 μ → MemLp C 2 μ →
    covariance A B μ = 0 → covariance A C μ = 0 → covariance B C μ = 0 →
    covariance (fun ω => A ω-C ω) (fun ω => B ω-C ω) μ = variance C μ

/-- Independent observations with common variance give the stated arm formulas. -/
def IndependentArmLaw : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n0 n1 n2 : ℕ), 0 < n0 → 0 < n1 → 0 < n2 →
    ∀ (X : (Fin n0 ⊕ (Fin n1 ⊕ Fin n2)) → Ω → ℝ),
    (∀ i, MemLp (X i) 2 μ) →
    Pairwise (fun i j => IndepFun (X i) (X j) μ) →
    ∀ (sigmaSq : ℝ), 0 < sigmaSq → (∀ i, variance (X i) μ = sigmaSq) →
    let C := armSampleMean (fun i => X (Sum.inl i))
    let A := armSampleMean (fun i => X (Sum.inr (Sum.inl i)))
    let B := armSampleMean (fun i => X (Sum.inr (Sum.inr i)))
    let D1 := fun ω => A ω-C ω
    let D2 := fun ω => B ω-C ω
    variance D1 μ = sigmaSq*(1/(n1:ℝ)+1/(n0:ℝ)) ∧
    variance D2 μ = sigmaSq*(1/(n2:ℝ)+1/(n0:ℝ)) ∧
    covariance D1 D2 μ = sigmaSq/(n0:ℝ) ∧
    effectCorrelation μ D1 D2 = Real.sqrt
      ((n1:ℝ)*(n2:ℝ)/(((n1:ℝ)+(n0:ℝ))*((n2:ℝ)+(n0:ℝ))))

/-- Marginal standard deviations bound covariance and the pooled variance;
one common centered unit-variance factor attains the bound. -/
def CovarianceBoundLaw : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ℕ) (a s : Fin J → ℝ) (D : Fin J → Ω → ℝ),
    (∀ j, MemLp (D j) 2 μ) → (∀ j, 0 ≤ a j) → (∀ j, 0 < s j) →
    (∀ j, variance (D j) μ = (s j)^2) →
    (∀ j k, |covariance (D j) (D k) μ| ≤ s j*s k) ∧
    variance (pooled a D) μ ≤ (∑ j, a j*s j)^2 ∧
    (∀ (Z : Ω → ℝ), MemLp Z 2 μ → (∫ ω, Z ω ∂μ) = 0 → variance Z μ = 1 →
      (∀ j, (fun ω => D j ω-(∫ x, D j x ∂μ)) =ᵐ[μ] (fun ω => s j*Z ω)) →
      variance (pooled a D) μ = (∑ j, a j*s j)^2)

end
end SAP.P042
