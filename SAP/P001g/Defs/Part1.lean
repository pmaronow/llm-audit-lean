import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P001g

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w z u1 v1

/-! Probability, sampling, conditional means, and the displayed estimators. -/

def prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) : ℝ := (μ A).toReal

def mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : ℝ := ∫ ω, X ω ∂μ

def var {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : ℝ := ProbabilityTheory.variance X μ

def cdf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ := prob μ {ω | X ω  ≤  x}

def CP {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (c : E) : Prop :=
  ∀ ε : ℝ, 0  <  ε → Tendsto (fun (n : ℕ) => prob μ {ω | ε  ≤  dist (Z n ω) c}) atTop (nhds 0)

def CD {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : ℕ → Ω → ℝ) (ν : Measure ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt (fun t => prob ν (Set.Iic t)) x →
    Tendsto (fun (n : ℕ) => cdf μ (Z n) x) atTop (nhds (prob ν (Set.Iic x)))

def IID {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  (∀ i, Measurable (X i)) ∧ iIndepFun X μ ∧ ∀ i, IdentDistrib (X i) (X 0) μ μ

def sampleMean {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X i ω) / (n : ℝ)

def empirical {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Measure ℝ :=
  (n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (X i ω)

def HasPDF (ν : Measure ℝ) (f : ℝ → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ x, 0  ≤  f x) ∧ Integrable f volume ∧
    ν = volume.withDensity (fun x => ENNReal.ofReal (f x))

def IsCEF {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y : Ω → ℝ) (m : E → ℝ) : Prop :=
  Measurable m ∧ Integrable Y μ ∧ Integrable (m ∘ X) μ ∧ ∀ A : Set E, MeasurableSet A →
    (∫ ω in X ⁻¹' A, Y ω ∂μ) = ∫ ω in X ⁻¹' A, m (X ω) ∂μ

def CI {Ω E F G : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace G] (μ : Measure Ω)
    (X : Ω → E) (hX : Measurable X) (Y : Ω → F) (Z : Ω → G) : Prop :=
  ∀ (A : Set F) (B : Set G), MeasurableSet A → MeasurableSet B →
    (μ[(fun ω => if Y ω∈A ∧ Z ω∈B then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]) =ᵐ[μ]
    (fun ω => (μ[(fun ω => if Y ω∈A then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]) ω *
      (μ[(fun ω => if Z ω∈B then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]) ω)

def firstSample {Ω E : Type*} (Z : ℕ → Ω → E) (n : ℕ) (ω : Ω) : Fin n → E :=
  fun i => Z i ω

def observedOutcome (y0 y1 d : ℝ) : ℝ := y1*d+y0*(1-d)

def censored (y r : ℝ) : ℝ := y*r+(-99)*(1-r)

def missingEndpoint (ystar r c : ℝ) : ℝ := ystar*r+c*(1-r)

def conditionalMeanAt {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → E) (Y : Ω → ℝ) (x : E) : ℝ :=
  (∫ ω in {ω | X ω=x},Y ω ∂μ)/prob μ {ω | X ω=x}

def standardizedMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (sampleMean X n ω-mean μ (sampleMean X n))/Real.sqrt (var μ (sampleMean X n))

def VarianceConsistent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (vhat : ℕ → Ω → ℝ) (v : ℝ) : Prop :=
  CP μ (fun n ω => (n : ℝ)*vhat n ω) v

def kernelDensity {n : ℕ} (K : ℝ → ℝ) (h : ℝ) (X : Fin n → ℝ) (x : ℝ) : ℝ :=
  (∑ i, K ((x-X i)/h)/h)/(n : ℝ)

def rectangleKernel (t : ℝ) : ℝ := if |t| ≤ 1 then 1/2 else 0
end

end SAP.P001g
