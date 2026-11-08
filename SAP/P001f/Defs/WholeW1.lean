import Mathlib
import SAP.P001f.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001f

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
universe u v
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The number of observations in a covariate cell, represented in the reals. -/
def wholeCellSize {n : ℕ} {E : Type*} (X : Fin n → E) (x : E) : ℝ :=
  ∑ i, if X i = x then 1 else 0

/-- The treated mass in an actual binary sample. -/
def wholeTreatedCount {n : ℕ} {E : Type*} (X : Fin n → E) (D : Fin n → ℝ)
    (x : E) : ℝ := ∑ i, if X i = x then D i else 0

/-- Real subtraction, rather than truncated natural subtraction. -/
def wholeControlCount {n : ℕ} {E : Type*} (X : Fin n → E) (D : Fin n → ℝ)
    (x : E) : ℝ := wholeCellSize X x - wholeTreatedCount X D x

def wholeTreatedSum {n : ℕ} {E : Type*} (X : Fin n → E) (D Y : Fin n → ℝ)
    (x : E) : ℝ := ∑ i, if X i = x then Y i * D i else 0

def wholeControlSum {n : ℕ} {E : Type*} (X : Fin n → E) (D Y : Fin n → ℝ)
    (x : E) : ℝ := ∑ i, if X i = x then Y i * (1 - D i) else 0

/-- Definition 7.2.6 on the individual observations. -/
def wholeUnitIPW {n : ℕ} {E : Type*} (X : Fin n → E) (D Y : Fin n → ℝ)
    (q : E → ℝ) : ℝ :=
  (∑ i, (Y i * D i / q (X i) - Y i * (1 - D i) / (1 - q (X i)))) / n

/-- Section 7.2.1's difference of empirical arm conditional means. The finite
cell type is the observed support, as expressed by surjectivity in T97. -/
def wholeCausalPlugin {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (X : Fin n → E) (D Y : Fin n → ℝ) : ℝ :=
  poststratifiedAverage Y D X - poststratifiedAverage Y (fun i => 1 - D i) X

def wholeCausalExampleX : Fin 6 → Fin 2 := ![1, 0, 0, 1, 1, 1]

/-- P001-T97, corrected Section 7.2.6, p. 266 (PDF p. 284), Section 7.2.1,
p. 256, and Example 7.2.1, p. 257: for every positive-size binary sample with
both arms in each observed cell, the individual IPW and empirical plug-in
estimators have the displayed cell formulas; saturated fitted propensities
make them equal, and equality for every individual outcome vector holds if
and only if the fitted propensity is the observed treated fraction in each
cell. The specified six-unit plug-in estimate is 4/9.
The usual measure-theoretic conditions are assumed. -/
def T97WholeStatement : Prop :=
  (∀ {n : ℕ} {E : Type v} [Fintype E] [DecidableEq E], 0 < n →
    ∀ (X : Fin n → E) (D : Fin n → ℝ) (q : E → ℝ),
    Function.Surjective X → (∀ i, D i = 0 ∨ D i = 1) →
    (∀ x, 0 < wholeTreatedCount X D x) →
    (∀ x, 0 < wholeControlCount X D x) →
    (∀ x, q x ∈ Set.Ioo (0 : ℝ) 1) →
    (∀ Y : Fin n → ℝ,
      wholeUnitIPW X D Y q =
        (∑ x, (wholeTreatedSum X D Y x / q x -
          wholeControlSum X D Y x / (1 - q x))) / n ∧
      wholeCausalPlugin X D Y =
        (∑ x, wholeCellSize X x *
          (wholeTreatedSum X D Y x / wholeTreatedCount X D x -
            wholeControlSum X D Y x / wholeControlCount X D x)) / n) ∧
    ((∀ x, q x = wholeTreatedCount X D x / wholeCellSize X x) →
      ∀ Y : Fin n → ℝ, wholeUnitIPW X D Y q = wholeCausalPlugin X D Y) ∧
    ((∀ Y : Fin n → ℝ, wholeUnitIPW X D Y q = wholeCausalPlugin X D Y) ↔
      ∀ x, q x = wholeTreatedCount X D x / wholeCellSize X x)) ∧
  wholeCausalPlugin wholeCausalExampleX exampleIndicator exampleOutcome =
    ((1 - 1) * (2 / 6) + (2 / 3 - 0) * (4 / 6) : ℝ) ∧
  wholeCausalPlugin wholeCausalExampleX exampleIndicator exampleOutcome = 4 / 9

/-- P001-T101, corrected set-subtraction row, p. 283 (PDF p. 301): relative
complement is membership in A outside B and intersection with U minus B.
The printed union identity holds exactly when A and B cover U and are
disjoint, equivalently when A is U minus B. For U={1,2,3}, A={1,2}, B={2},
the difference and intersection are {1}, and the union is {1,2,3}.
The usual measure-theoretic conditions are assumed. -/
def T101WholeStatement : Prop :=
  (∀ {Ω : Type u} (U A B : Set Ω), A ⊆ U → B ⊆ U →
    A \ B = {s | s ∈ A ∧ s ∉ B} ∧ A \ B = A ∩ (U \ B) ∧
    (A \ B = A ∪ (U \ B) ↔ A ∪ B = U ∧ A ∩ B = ∅) ∧
    (A \ B = A ∪ (U \ B) ↔ A = U \ B) ∧
    (A ∪ B = U ∧ A ∩ B = ∅ ↔ A = U \ B)) ∧
  (({1, 2} : Set ℕ) \ {2} = {1} ∧
    ({1, 2} : Set ℕ) ∩ ({1, 2, 3} \ {2}) = {1} ∧
    ({1, 2} : Set ℕ) ∪ ({1, 2, 3} \ {2}) = {1, 2, 3})

/-- P001-T107, Theorems 2.2.17–18 and 2.2.20, pp. 72–73 and 75–76
(PDF pp. 90–91 and 93–94): iterated expectation holds; with a finite second
moment, total variance is expected conditional variance plus variance of the
CEF. For every measurable predictor with finite prediction MSE, the exact
MSE decomposition has a nonnegative remainder, the CEF minimizes MSE, and
its residual risk equals expected conditional variance. The prediction
assertion needs finite squared residuals, not a second moment of Y.
The usual measure-theoretic conditions are assumed. -/
def T107WholeStatement : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (Y : Ω → ℝ),
    Measurable X → Measurable Y → Integrable Y μ →
    ∀ m : E → ℝ, ConditionalMean μ X Y m →
    (∫ ω, Y ω ∂μ) = (∫ ω, m (X ω) ∂μ) ∧
    (MemLp Y 2 μ → MemLp (m ∘ X) 2 μ ∧
      ∀ v : E → ℝ, ConditionalMean μ X (fun ω => (Y ω - m (X ω)) ^ 2) v →
        variance Y μ = (∫ ω, v (X ω) ∂μ) + variance (m ∘ X) μ) ∧
    (∀ v : E → ℝ, ConditionalMean μ X (fun ω => (Y ω - m (X ω)) ^ 2) v →
      ∀ g : E → ℝ, Measurable g →
      Integrable (fun ω => (Y ω - g (X ω)) ^ 2) μ →
      Integrable (fun ω => (m (X ω) - g (X ω)) ^ 2) μ ∧
      (∫ ω, (Y ω - g (X ω)) ^ 2 ∂μ) = (∫ ω, v (X ω) ∂μ) +
        (∫ ω, (m (X ω) - g (X ω)) ^ 2 ∂μ) ∧
      0 ≤ (∫ ω, (m (X ω) - g (X ω)) ^ 2 ∂μ) ∧
      (∫ ω, (Y ω - m (X ω)) ^ 2 ∂μ) ≤ (∫ ω, (Y ω - g (X ω)) ^ 2 ∂μ) ∧
      (∫ ω, v (X ω) ∂μ) ≤ (∫ ω, (Y ω - g (X ω)) ^ 2 ∂μ) ∧
      (∫ ω, v (X ω) ∂μ) = (∫ ω, (Y ω - m (X ω)) ^ 2 ∂μ))

/-- The average of a fixed finite family on its original probability space. -/
def wholeFiniteAverage {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ i, X i ω) / n

/-- P001-T108, Theorems 3.2.3–5, pp. 97–99 (PDF pp. 115–117): every
positive-size finite measurable iid family has an integrable sample mean
with the common population expectation under a first moment. Under a second
moment its variance is the population variance divided by n, and with
positive population variance it obeys the displayed Chebyshev bound.
The usual measure-theoretic conditions are assumed. -/
def T108WholeStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ}, 0 < n → ∀ (X : Fin n → Ω → ℝ) (j : Fin n),
    (∀ i, Measurable (X i)) → iIndepFun X μ →
    (∀ i, IdentDistrib (X i) (X j) μ μ) → Integrable (X j) μ →
    Integrable (wholeFiniteAverage X) μ ∧
    (∫ ω, wholeFiniteAverage X ω ∂μ) = (∫ ω, X j ω ∂μ) ∧
    (MemLp (X j) 2 μ →
      MemLp (wholeFiniteAverage X) 2 μ ∧
      variance (wholeFiniteAverage X) μ = variance (X j) μ / n ∧
      (0 < variance (X j) μ → ∀ ε : ℝ, 0 < ε →
        (μ {ω | ε ≤ |wholeFiniteAverage X ω - ∫ z, X j z ∂μ|}).toReal ≤
          variance (X j) μ / (ε ^ 2 * (n : ℝ))))

/-- Empirical support; no finiteness assumption on the ambient covariate type. -/
def wholeObservedCells {n : ℕ} {E : Type*} (X : Fin n → E) : Finset E :=
  Finset.univ.image X

/-- Section 6.2.1's empirical mean, summed over exactly the observed profiles. -/
def wholeResponsePlugin {n : ℕ} {E : Type*} (ystar r : Fin n → ℝ)
    (X : Fin n → E) : ℝ :=
  ∑ x ∈ wholeObservedCells X,
    (wholeTreatedSum X r ystar x / wholeTreatedCount X r x) *
      (wholeCellSize X x / n)

/-- Positive-mass support, excluding the zero-probability conditional values. -/
def wholeMassSupport {Ω E : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → E) : Set E :=
  {x | 0 < (μ {ω | X ω = x}).toReal}

/-- MAR identification without a separate population moment premise on the
respondent regression; discrete vectors are represented by countable range. -/
def wholeVectorMAR : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y R : Ω → ℝ),
    Measurable Y → Measurable R → Integrable Y μ →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < (μ {ω | R ω = 0}).toReal → 0 < (μ {ω | R ω = 1}).toReal →
    ∀ p m : (Fin K → ℝ) → ℝ, ConditionalMean μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    ConditionallyIndependent μ X hX Y R →
    ConditionalMean (μ.restrict {ω | R ω = 1}) X
      (fun ω => censoredOutcome (Y ω) (R ω)) m →
    Integrable (m ∘ X) μ ∧ ConditionalMean μ X Y m ∧
    (∫ ω, Y ω ∂μ) = (∫ ω, m (X ω) ∂μ) ∧
    (Set.Countable (Set.range X) →
      Summable (fun x : wholeMassSupport μ X => m x * (μ {ω | X ω = x}).toReal) ∧
      Summable (fun x : wholeMassSupport μ X => |m x| * (μ {ω | X ω = x}).toReal) ∧
      (∫ ω, Y ω ∂μ) =
        ∑' x : wholeMassSupport μ X, m x * (μ {ω | X ω = x}).toReal)

/-- P001-T111, Theorems 6.1.6, 6.1.9–10, pp. 213 and 216–217
(PDF pp. 231 and 234–235), with Examples 6.1.7 and 6.2.1, pp. 214 and
220: MCAR identifies the mean by respondents; MAR and uniform response
overlap identify the vector CEF and the discrete positive-support mean,
with population integrability derived rather than assumed. The empirical
respondent and observed-profile formulas hold whenever their denominators
are positive, and the six-unit estimates are 3/4 and 7/9.
The usual measure-theoretic conditions are assumed. -/
def T111WholeStatement : Prop :=
  MCARMean.{u} ∧ wholeVectorMAR.{u} ∧
  (∀ {n : ℕ}, 0 < n → ∀ y r : Fin n → ℝ,
    (∀ i, r i = 0 ∨ r i = 1) → 0 < ∑ i, r i →
    respondentAverage (fun i => censoredOutcome (y i) (r i)) r =
      (∑ i, censoredOutcome (y i) (r i) * r i) / (∑ i, r i)) ∧
  (∀ {n K : ℕ}, 0 < n → ∀ (y r : Fin n → ℝ) (X : Fin n → Fin K → ℝ),
    (∀ i, r i = 0 ∨ r i = 1) →
    (∀ x ∈ wholeObservedCells X, 0 < wholeTreatedCount X r x) →
    wholeResponsePlugin (fun i => censoredOutcome (y i) (r i)) r X =
      ∑ x ∈ wholeObservedCells X,
        ((∑ i, if X i = x then censoredOutcome (y i) (r i) * r i else 0) /
          (∑ i, if X i = x then r i else 0)) *
          ((∑ i, if X i = x then (1 : ℝ) else 0) / n)) ∧
  respondentAverage exampleCensored exampleIndicator = 3 / 4 ∧
  wholeResponsePlugin exampleCensored exampleIndicator exampleCovariate =
    (2 / 3 : ℝ) * (4 / 6) + 1 * (2 / 6) ∧
  wholeResponsePlugin exampleCensored exampleIndicator exampleCovariate = 7 / 9

end
end SAP.P001f
