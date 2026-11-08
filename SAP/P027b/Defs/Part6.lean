import SAP.P027b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

/-- Moment hypotheses of the ordinary common-stratum pair correlation. -/
def PairMoments {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) (S ε ε' : Ξ → ℝ) : Prop :=
  (∀ᵐ ξ ∂μ, S ξ = 1 ∨ S ξ = -1) ∧ outcomeE μ S = 0 ∧ Integrable S μ ∧
  Integrable ε μ ∧ Integrable ε' μ ∧
  (outcomeE μ ε = 0 ∧ outcomeE μ ε' = 0) ∧
  (Integrable (fun ξ => ε ξ^2) μ ∧ Integrable (fun ξ => ε' ξ^2) μ ∧
    outcomeE μ (fun ξ => ε ξ^2) = 1 ∧ outcomeE μ (fun ξ => ε' ξ^2) = 1) ∧
  (Integrable (fun ξ => S ξ*ε ξ) μ ∧ Integrable (fun ξ => S ξ*ε' ξ) μ ∧
    Integrable (fun ξ => ε ξ*ε' ξ) μ ∧ outcomeE μ (fun ξ => S ξ*ε ξ) = 0 ∧
    outcomeE μ (fun ξ => S ξ*ε' ξ) = 0 ∧ outcomeE μ (fun ξ => ε ξ*ε' ξ) = 0)

/-- Zero means make the displayed second and cross moments variances and covariance. -/
def PairCorrelation {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (α : ℝ) (S ε ε' : Ξ → ℝ) : Prop :=
  let Y := fun ξ => α*S ξ+ε ξ
  let Y' := fun ξ => α*S ξ+ε' ξ
  outcomeE μ Y = 0 ∧ outcomeE μ Y' = 0 ∧
  outcomeE μ (fun ξ => Y ξ^2) = α^2+1 ∧
  outcomeE μ (fun ξ => Y' ξ^2) = α^2+1 ∧
  outcomeE μ (fun ξ => Y ξ*Y' ξ) = α^2 ∧
  outcomeE μ (fun ξ => Y ξ*Y' ξ)/
    Real.sqrt (outcomeE μ (fun ξ => Y ξ^2)*outcomeE μ (fun ξ => Y' ξ^2)) =
    pairCorrelationFormula α

/-- All four mathematical clauses, including the six label conversions and limit. -/
def T17Statement : Prop :=
  (∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (α : ℝ) (S ε ε' : Ξ → ℝ), PairMoments μ S ε ε' → PairCorrelation μ α S ε ε') ∧
  (∀ α : ℝ,
    (∑ s, stratumMeans α s)/2 = 0 ∧ stratumMeansVariance α = 2*α^2 ∧
    heterogeneity α = stratumMeansVariance α/(stratumMeansVariance α+1) ∧
    heterogeneity α = (2*α^2)/(2*α^2+1) ∧
    heterogeneity α-pairCorrelationFormula α = α^2/((α^2+1)*(2*α^2+1)) ∧
    0 ≤ heterogeneity α-pairCorrelationFormula α ∧
    (heterogeneity α = pairCorrelationFormula α ↔ α = 0) ∧
    pairCorrelationFormula α = heterogeneity α/(2-heterogeneity α) ∧
    α^2 = heterogeneity α/(2*(1-heterogeneity α))) ∧
  StrictMonoOn (fun q : ℝ => q/(2-q)) (Set.Ico 0 1) ∧
  Tendsto (fun q : ℝ => q/(2-q)) (𝓝[<] 1) (𝓝 1) ∧
  (0.33:ℝ)/(2-0.33) = 33/167 ∧ (0.50:ℝ)/(2-0.50) = 1/3 ∧
  (0.67:ℝ)/(2-0.67) = 67/133 ∧ (0.82:ℝ)/(2-0.82) = 41/59 ∧
  (0.90:ℝ)/(2-0.90) = 9/11 ∧ (0.99:ℝ)/(2-0.99) = 99/101

end
end SAP.P027b
