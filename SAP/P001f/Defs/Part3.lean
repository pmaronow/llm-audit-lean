import SAP.P001f.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001f

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
universe u v

/-- The grouped eighteen-unit counterexample, including its actual unique logit fit. -/
def T96Statement : Prop :=
  ((∀ a b : ℝ,
    groupedLogLikelihood causalSizes causalTreatedCounts a b ≤
      groupedLogLikelihood causalSizes causalTreatedCounts 0 (Real.log 2) ∧
    (groupedLogLikelihood causalSizes causalTreatedCounts a b =
      groupedLogLikelihood causalSizes causalTreatedCounts 0 (Real.log 2) ↔
      a = 0 ∧ b = Real.log 2)) ∧
   (∀ j : Fin 3, 0 < causalTreatedCounts j ∧ causalTreatedCounts j < causalSizes j ∧
     logisticProbability 0 (Real.log 2) ((![-1, 0, 1] : Fin 3 → ℝ) j) =
       ((![1 / 3, 1 / 2, 2 / 3] : Fin 3 → ℝ) j)) ∧
   (∑ j, (causalTreatedSums j /
       logisticProbability 0 (Real.log 2) ((![-1, 0, 1] : Fin 3 → ℝ) j) -
     causalControlSums j /
       (1 - logisticProbability 0 (Real.log 2) ((![-1, 0, 1] : Fin 3 → ℝ) j)))) / 18 = 59 / 36 ∧
   (∑ j, causalSizes j * (causalTreatedSums j / causalTreatedCounts j -
      causalControlSums j / (causalSizes j - causalTreatedCounts j))) / 18 = 1 ∧
   (59 / 36 : ℝ) ≠ 1) ∧
  (∀ j : Fin 3, causalTreatedCounts j / causalSizes j =
    ((![1 / 2, 1 / 6, 5 / 6] : Fin 3 → ℝ) j)) ∧
  (3 - 6 * (1 / 3 : ℝ) = 1 ∧ 1 - 6 * (1 / 2 : ℝ) = -2 ∧
    5 - 6 * (2 / 3 : ℝ) = 1 ∧ (1 - 2 + 1 : ℝ) = 0 ∧ (-1 + 0 + 1 : ℝ) = 0) ∧
  (((3 * 4 / (1 / 3) - 3 * 3 / (2 / 3)) + (1 * 3 / (1 / 2) - 5 * 2 / (1 / 2)) +
      (5 * 4 / (2 / 3) - 1 * 3 / (1 / 3)) : ℝ) / 18 = 59 / 36 ∧
    ((6 / 18) * (4 - 3) + (6 / 18) * (3 - 2) + (6 / 18) * (4 - 3) : ℝ) = 1 ∧
    (59 / 36 : ℝ) ≠ 1) ∧
  ((59 / 36 : ℝ) - 1 = 23 / 36 ∧ (23 / 36 : ℝ) ≠ 0)

/-- Equality as an identity in cell outcome sums characterizes saturated propensities. -/
def T97Statement : Prop :=
  ∀ {E : Type v} [Fintype E] [DecidableEq E] (n : ℕ), 0 < n →
    ∀ nt nc q : E → ℝ, (∀ x, 0 < nt x) → (∀ x, 0 < nc x) →
    (∀ x, q x ∈ Set.Ioo (0 : ℝ) 1) →
    ((∀ st sc : E → ℝ, cellIPW n q st sc = cellPoststratification n nt nc st sc) ↔
      ∀ x, q x = nt x / (nt x + nc x))

/-- True-score conditional means, sample expectations and the erroneous reciprocal weights. -/
def T98Statement : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → E) (D : ℕ → Ω → ℝ),
    IndependentCopies μ (fun i ω => (X i ω, D i ω)) →
    ∀ p : E → ℝ, ConditionalMean μ (X 0) (D 0) p →
    (∀ i ω, D i ω = 0 ∨ D i ω = 1) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ i ω, ε < p (X i ω) ∧ p (X i ω) < 1 - ε) →
    (ConditionalMean μ (X 0) (fun ω => D 0 ω / p (X 0 ω)) (fun _ => 1) ∧
      ConditionalMean μ (X 0) (fun ω => (1 - D 0 ω) / (1 - p (X 0 ω))) (fun _ => 1) ∧
      (∫ ω, D 0 ω / p (X 0 ω) ∂μ) = 1 ∧
      (∫ ω, (1 - D 0 ω) / (1 - p (X 0 ω)) ∂μ) = 1) ∧
    (∀ n, 0 < n →
      (∫ ω, sampleAverage (fun i z => D i z / p (X i z)) n ω ∂μ) = 1 ∧
      (∫ ω, sampleAverage (fun i z => (1 - D i z) / (1 - p (X i z))) n ω ∂μ) = 1) ∧
    1 < (∫ ω, 1 / p (X 0 ω) ∂μ) ∧ 1 < (∫ ω, 1 / (1 - p (X 0 ω)) ∂μ)

/-- A two-point law with constant potential outcomes separates the unnormalized estimand from ATT. -/
def T99Statement : Prop :=
  (∀ i, 0 ≤ attWeights i) ∧ (∑ i, attWeights i) = 1 ∧
  finiteProbability attWeights (fun i => (![0, 1] : Fin 2 → ℝ) i = 0) = 3 / 4 ∧
  finiteProbability attWeights (fun i => (![0, 1] : Fin 2 → ℝ) i = 1) = 1 / 4 ∧
  FiniteConditionalIndependence attWeights (fun _ => ((0 : ℝ), (1 : ℝ)))
    (![0, 1] : Fin 2 → ℝ) (fun _ => (0 : ℝ)) ∧
  finiteEventMean attWeights (![0, 1] : Fin 2 → ℝ) (fun _ => 0) 0 = 1 / 4 ∧
  ((1 / 8 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) < 1 - 1 / 8) ∧
  ((1 / 4 : ℝ) < 3 / 8 ∧ (3 / 8 : ℝ) < 1) ∧
  finiteMean attWeights (fun _ => (1 / 4 : ℝ) * (1 - 0)) = 1 / 4 ∧
  finiteEventMean attWeights (fun _ => 1) (![0, 1] : Fin 2 → ℝ) 1 = 1 ∧
  finiteMean attWeights (fun _ => (1 / 4 : ℝ) * (1 - 0)) ≠
    finiteEventMean attWeights (fun _ => 1 - 0) (![0, 1] : Fin 2 → ℝ) 1 ∧
  finiteMean attWeights (fun _ => (1 / 4 : ℝ) * 1) /
    finiteMean attWeights (fun _ => (1 / 4 : ℝ)) =
      finiteEventMean attWeights (fun _ => 1) (![0, 1] : Fin 2 → ℝ) 1

def T100Statement : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y0 Y1 D : Ω → ℝ), Measurable Y0 → Measurable Y1 → Measurable D →
    Integrable (fun ω => Y1 ω - Y0 ω) μ → (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    (0 < (μ {ω | D ω = 1}).toReal ∧ (μ {ω | D ω = 1}).toReal < 1) →
    ∀ p : E → ℝ, ConditionalMean μ X D p →
    ConditionallyIndependent μ X hX (fun ω => (Y0 ω, Y1 ω)) D →
    let P := (μ {ω | D ω = 1}).toReal
    let W := ∫ ω, p (X ω) * (Y1 ω - Y0 ω) ∂μ
    let A := eventMean μ D (fun ω => Y1 ω - Y0 ω) 1
    (∫ ω, p (X ω) ∂μ) = P ∧ 0 < P ∧
    W = (∫ ω, D ω * (Y1 ω - Y0 ω) ∂μ) ∧ W = P * A ∧
    A = W / (∫ ω, p (X ω) ∂μ) ∧ (W = A ↔ P = 1 ∨ A = 0)

def T101Statement : Prop :=
  ∀ {Ω : Type u} (A B : Set Ω),
    A \ B = {s | s ∈ A ∧ s ∉ B} ∧ A \ B = A ∩ Bᶜ

def T102Statement : Prop :=
  ¬ PDAIdentifiedPDFSupportSaturated.{u} ∧
  ∀ {Ω : Type u} {K : ℕ} (X : ℕ → Ω → Fin K → ℝ)
    (mhat : ℕ → Ω → (Fin K → ℝ) → ℝ) (n : ℕ), 0 < n →
    ∀ (ω : Ω) (k : Fin K),
    DifferentiableAt ℝ (fun t => mhat n ω
      (Function.update (fun j => sampleAverage (fun i z => X i z j) n ω) k
        (sampleAverage (fun i z => X i z k) n ω + t))) 0 →
    samplePDA X mhat n ω k = coordinateDerivative (mhat n ω)
      (fun j => sampleAverage (fun i z => X i z j) n ω) k

def T103Statement : Prop :=
  ¬ ∀ {n : ℕ}, 0 < n → ∀ y : Fin n → ℝ, (∀ i, 0 < y i) →
    ∃ θ : Fin 7 → ℝ, ValidMixture θ ∧ ∀ θ', ValidMixture θ' →
      mixtureSampleLikelihood y θ' ≤ mixtureSampleLikelihood y θ

def T104Statement : Prop := ¬ OverlapUniformPositivityEquivalence

end
end SAP.P001f
