import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical
noncomputable section

/-- Real event probability; all statements below use probability measures. -/
def probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) : ℝ :=
  (μ A).toReal

def expectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  ∫ ω, X ω ∂μ

def meanSquaredError {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (c : ℝ) : ℝ := ∫ ω, (X ω - c)^2 ∂μ

def cdfAt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ :=
  probability μ {ω | X ω ≤ x}

/-- Definition 3.2.6, with its bad-event formulation. -/
def convergesInProbability {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (c : E) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => probability μ {ω | ε ≤ dist (Z n ω) c}) atTop (nhds 0)

/-- Distributional convergence at continuity points of the limiting CDF. -/
def convergesInDistribution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : ℕ → Ω → ℝ) (ν : Measure ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt (fun t => probability ν (Set.Iic t)) x →
    Tendsto (fun n => cdfAt μ (Z n) x) atTop (nhds (probability ν (Set.Iic x)))

def isIID {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  (∀ i, Measurable (X i)) ∧ iIndepFun X μ ∧ ∀ i, IdentDistrib (X i) (X 0) μ μ

/-- The first n observations are indexed from zero. -/
def sampleAverage {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X i ω) / (n : ℝ)

/-- Used as a probability law only for positive sample sizes. -/
def empiricalLaw {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Measure ℝ :=
  (n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (X i ω)

def pluginVariance {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sampleAverage (fun i ω => (X i ω)^2) n ω - (sampleAverage X n ω)^2

def correlationCoefficient {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  covariance X Y μ / (Real.sqrt (variance X μ) * Real.sqrt (variance Y μ))

def affineRisk {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (a b : ℝ) : ℝ :=
  expectation μ (fun ω => (Y ω - a - b * X ω)^2)

def regressionSlope {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ := covariance X Y μ / variance X μ

def regressionIntercept {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  expectation μ Y - regressionSlope μ X Y * expectation μ X

/-- A version of a conditional mean, specified by event integrals. -/
def isConditionalMean {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y : Ω → ℝ) (m : E → ℝ) : Prop :=
  Measurable m ∧ Integrable Y μ ∧ Integrable (m ∘ X) μ ∧
    ∀ A : Set E, MeasurableSet A →
      (∫ ω in X ⁻¹' A, Y ω ∂μ) = ∫ ω in X ⁻¹' A, m (X ω) ∂μ

def varianceConsistent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : ℕ → Ω → ℝ) (v : ℝ) : Prop :=
  convergesInProbability μ (fun n ω => (n : ℝ) * V n ω) v

def standardErrorConsistent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : ℕ → Ω → ℝ) (v : ℝ) : Prop :=
  convergesInProbability μ (fun n ω => Real.sqrt n * Real.sqrt (V n ω)) (Real.sqrt v)

end
end SAP.P001c
