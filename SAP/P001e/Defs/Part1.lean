import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e
universe u v
noncomputable section

def probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) : ℝ := (μ A).toReal

def expectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : ℝ := ∫ ω, X ω ∂μ

def ConvergesInProbability {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (c : E) : Prop :=
  ∀ ε : ℝ, 0  <  ε → Tendsto (fun (n : ℕ) => probability μ {ω | ε  ≤  dist (Z n ω) c}) atTop (nhds 0)

def IsIID {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  (∀ i, Measurable (X i)) ∧ iIndepFun X μ ∧ ∀ i, IdentDistrib (X i) (X 0) μ μ

def sampleAverage {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X i ω) / (n : ℝ)

def IsConditionalMean {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y : Ω → ℝ) (m : E → ℝ) : Prop :=
  Measurable m ∧ Integrable Y μ ∧ Integrable (m ∘ X) μ ∧ ∀ A : Set E, MeasurableSet A →
    (∫ ω in X ⁻¹' A, Y ω ∂μ) = ∫ ω in X ⁻¹' A, m (X ω) ∂μ

def CondIndependent {Ω E F G : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace G] (μ : Measure Ω)
    (X : Ω → E) (hX : Measurable X) (Y : Ω → F) (Z : Ω → G) : Prop :=
  ∀ (A : Set F) (B : Set G), MeasurableSet A → MeasurableSet B →
    (μ[(fun ω => if Y ω∈A ∧ Z ω∈B then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]) =ᵐ[μ]
    (fun ω => (μ[(fun ω => if Y ω∈A then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]) ω *
      (μ[(fun ω => if Z ω∈B then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]) ω)

def residualSS {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ) (b : Fin (K+1) → ℝ) : ℝ :=
  ∑ i,(Y i-(X.mulVec b) i)^2

def leastSquaresCoef {n K : ℕ} (X : Matrix (Fin n) (Fin K) ℝ) (Y : Fin n → ℝ) : Fin K → ℝ :=
  (X.transpose*X)⁻¹.mulVec (X.transpose.mulVec Y)

def gaussianLogLikelihood {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
    (b : Fin (K+1) → ℝ) (s : ℝ) : ℝ :=
  -(n : ℝ)*Real.log s-(n : ℝ)/2*Real.log (2*Real.pi)-residualSS X Y b/(2*s^2)

def fittedJointLaw {n K : ℕ} (X : Fin n → Fin K → ℝ) (ν : Fin n → Measure ℝ) : Measure (ℝ × (Fin K → ℝ)) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i,(ν i).prod (Measure.dirac (X i))

def recordedOutcome (y r : ℝ) : ℝ := y*r+(-99)*(1-r)

def completeMissing (ystar r c : ℝ) : ℝ := ystar*r+c*(1-r)

def realizedOutcome (y0 y1 d : ℝ) : ℝ := y1*d+y0*(1-d)

def lowerEffect (y d a b : ℝ) : ℝ := y*d+a*(1-d)-y*(1-d)-b*d

def upperEffect (y d a b : ℝ) : ℝ := y*d+b*(1-d)-y*(1-d)-a*d

def cellMean {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → E) (Y : Ω → ℝ) (x : E) : ℝ :=
  (∫ ω in {ω | X ω=x},Y ω ∂μ)/probability μ {ω | X ω=x}

def responseProbability {E : Type*} (κ : E → Measure Bool) (x : E) : ℝ := probability (κ x) {true}
end
end SAP.P001e
