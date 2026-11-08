import Mathlib
import SAP.P001e.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Classical

namespace SAP.P001e

universe u
noncomputable section

/-- The pooled linear regression, with an intercept, binary-treatment coefficient,
and an arbitrary finite number of covariates. -/
def pooledPredictionW4 {K : ℕ} (a b : ℝ) (c x : Fin K → ℝ) (d : ℝ) : ℝ :=
  a + b * d + ∑ k, x k * c k

/-- Residual sum of squares; no inverse matrix or rank assumption is used. -/
def pooledRSSW4 {n K : ℕ} (Y D : Fin n → ℝ) (X : Fin n → Fin K → ℝ)
    (a b : ℝ) (c : Fin K → ℝ) : ℝ :=
  ∑ i, (Y i - pooledPredictionW4 a b c (X i) (D i)) ^ 2

/-- An arbitrary global OLS minimizer, including when the design is singular. -/
def IsPooledOLSW4 {n K : ℕ} (Y D : Fin n → ℝ) (X : Fin n → Fin K → ℝ)
    (a b : ℝ) (c : Fin K → ℝ) : Prop :=
  ∀ (a' b' : ℝ) (c' : Fin K → ℝ),
    pooledRSSW4 Y D X a b c ≤ pooledRSSW4 Y D X a' b' c'

/-- Fill only a missing potential outcome, retaining every observed outcome. -/
def completedOutcomeW4 {n K : ℕ} (Y D : Fin n → ℝ) (X : Fin n → Fin K → ℝ)
    (a b : ℝ) (c : Fin K → ℝ) (d : ℝ) (i : Fin n) : ℝ :=
  if D i = d then Y i else pooledPredictionW4 a b c (X i) d

/-- The two completed columns of the corrected six-unit tables.
`missingOnly = true` retains observed outcomes; `false` imputes every entry. -/
def exampleCompletedW4 (missingOnly : Bool) (d : ℝ) (i : Fin 6) : ℝ :=
  if missingOnly = true ∧ exampleD i = d then exampleY i
  else examplePrediction (exampleX1 i) (exampleX2 i) d

/-- The deterministic fitted contrast used for both the conditional and marginal
plug-in estimates. This makes no statistical consistency assertion. -/
def FittedContrastW4 : Prop :=
  ∀ {K : ℕ} (a b : ℝ) (c x : Fin K → ℝ),
    pooledPredictionW4 a b c x 1 - pooledPredictionW4 a b c x 0 = b

/-- The sample identities for every OLS minimizer. Both arms are nonempty as in
the claim; no causal assumption, full-rank assumption, or uniqueness is required.
The completed-column means have denominator n, because each column contains all n units. -/
def FiniteImputationW4 : Prop :=
  ∀ {n K : ℕ} (Y D : Fin n → ℝ) (X : Fin n → Fin K → ℝ)
    (hbinary : ∀ i, D i = 0 ∨ D i = 1)
    (harms : (∃ i, D i = 0) ∧ (∃ i, D i = 1))
    (a b : ℝ) (c : Fin K → ℝ) (hfit : IsPooledOLSW4 Y D X a b c),
    let g := fun i => a + ∑ k, X i k * c k
    let e := fun i => Y i - g i - b * D i
    let correction := ((∑ i ∈ Finset.univ.filter (fun i => D i = 1), e i) -
      ∑ i ∈ Finset.univ.filter (fun i => D i = 0), e i) / (n : ℝ)
    let allEstimate := (∑ i, (pooledPredictionW4 a b c (X i) 1 -
      pooledPredictionW4 a b c (X i) 0)) / (n : ℝ)
    let missingEstimate := ((∑ i ∈ Finset.univ.filter (fun i => D i = 1),
      (Y i - a - (∑ k, X i k * c k))) +
      ∑ i ∈ Finset.univ.filter (fun i => D i = 0),
        (a + b + (∑ k, X i k * c k) - Y i)) / (n : ℝ)
    0 < n ∧ (∑ i, e i) = 0 ∧ (∑ i, e i * D i) = 0 ∧
    allEstimate = b ∧
    (∑ i, pooledPredictionW4 a b c (X i) 1) / (n : ℝ) -
      (∑ i, pooledPredictionW4 a b c (X i) 0) / (n : ℝ) = allEstimate ∧
    (∑ i, completedOutcomeW4 Y D X a b c 1 i) / (n : ℝ) -
      (∑ i, completedOutcomeW4 Y D X a b c 0 i) / (n : ℝ) = missingEstimate ∧
    missingEstimate = b + correction ∧ correction = 0 ∧ missingEstimate = b

/-- The population calculation assumes the corrected strong ignorability and
an exact observed conditional mean version. All binary and overlap conditions
are almost sure. No moment assumption on individual covariates is imposed.
The conclusion includes the armwise observed CEFs, potential-outcome CEFs,
the conditional contrast for almost every covariate value, and the ATE. -/
def PopulationLinearCEFW4 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K : ℕ} (X : Ω → Fin K → ℝ) (D Y0 Y1 : Ω → ℝ)
    (hX : Measurable X) (hD : Measurable D)
    (h0 : Measurable Y0) (h1 : Measurable Y1)
    (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ)
    (hbinary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (p : (Fin K → ℝ) → ℝ) (hp : IsConditionalMean μ X D p)
    (hpos : ∃ η : ℝ, 0 < η ∧
      ∀ᵐ ω ∂μ, η < p (X ω) ∧ p (X ω) < 1 - η)
    (hind : CondIndependent μ X hX (fun ω => (Y0 ω, Y1 ω)) D)
    (a b : ℝ) (c : Fin K → ℝ)
    (hcef : IsConditionalMean μ (fun ω => (D ω, X ω))
      (fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω))
      (fun dx => pooledPredictionW4 a b c dx.2 dx.1)),
    let Y := fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω)
    let m0 := fun x => pooledPredictionW4 a b c x 0
    let m1 := fun x => pooledPredictionW4 a b c x 1
    let τ := fun ω => Y1 ω - Y0 ω
    IsConditionalMean (μ.restrict {ω | D ω = 0}) X Y m0 ∧
    IsConditionalMean (μ.restrict {ω | D ω = 1}) X Y m1 ∧
    IsConditionalMean μ X Y0 m0 ∧ IsConditionalMean μ X Y1 m1 ∧
    IsConditionalMean μ X τ (fun x => m1 x - m0 x) ∧
    IsConditionalMean μ X τ (fun _ => b) ∧
    (μ[τ | MeasurableSpace.comap X inferInstance] =ᵐ[μ] (fun _ => b)) ∧
    (∀ t : (Fin K → ℝ) → ℝ, IsConditionalMean μ X τ t →
      ∀ᵐ x ∂(μ.map X), t x = m1 x - m0 x ∧ m1 x - m0 x = b ∧ t x = b) ∧
    expectation μ τ = b

/-- Every entry of both corrected imputation tables, their exact OLS fit, and
the two completed-column differences of means. Unit 3 is index 2 in `Fin 6`. -/
def CorrectedExampleW4 : Prop :=
  (exampleD 2, exampleX1 2, exampleX2 2) = (1, 10, 3) ∧
  exampleCompletedW4 true 0 =
    ![examplePrediction 1 7 0, 5, examplePrediction 10 3 0,
      examplePrediction 3 1 0, examplePrediction 5 2 0, 0] ∧
  exampleCompletedW4 true 1 =
    ![2, examplePrediction 8 2 1, 3, 10, 2, examplePrediction 7 0 1] ∧
  exampleCompletedW4 false 0 =
    ![examplePrediction 1 7 0, examplePrediction 8 2 0, examplePrediction 10 3 0,
      examplePrediction 3 1 0, examplePrediction 5 2 0, examplePrediction 7 0 0] ∧
  exampleCompletedW4 false 1 =
    ![examplePrediction 1 7 1, examplePrediction 8 2 1, examplePrediction 10 3 1,
      examplePrediction 3 1 1, examplePrediction 5 2 1, examplePrediction 7 0 1] ∧
  IsUnit (exampleDesign.transpose * exampleDesign).det ∧
  leastSquaresCoef exampleDesign exampleY = exampleCoef ∧
  exampleCoef = ![13563/2437, 6178/2437, -759/2437, -1778/2437] ∧
  partialImputation exampleX1 = 6178/2437 ∧ fullImputation exampleX1 = 6178/2437 ∧
  (∑ i, exampleCompletedW4 true 1 i) / 6 -
    (∑ i, exampleCompletedW4 true 0 i) / 6 = 6178/2437 ∧
  (∑ i, exampleCompletedW4 false 1 i) / 6 -
    (∑ i, exampleCompletedW4 false 0 i) / 6 = 6178/2437

/-- P001-T93; Example 7.2.2, pp. 258–259 (PDF pp. 276–277), corrected.
Both imputation tables use unit 3's covariates (10,3). For any pooled OLS
minimizer, imputing all potential outcomes and imputing only missing outcomes
give the same difference of completed-column means, the treatment coefficient;
the residual normal equations and the displayed filtered-sum correction hold.
The six-unit coefficients are (13563,6178,-759,-1778)/2437 and both estimates
are 6178/2437. Under strong ignorability with uniform overlap and an exact
linear observed CEF, the conditional ATE equals the armwise observed CEF
contrast and the treatment coefficient almost everywhere in the covariate law,
and the ATE equals that coefficient. The fitted contrast is that coefficient
at every covariate value. The usual measure-theoretic conditions are assumed.
“More straightforward to implement” describes the two displayed algorithms;
it makes no mathematical comparison of computational costs. -/
def T93WholeStatement_W4 : Prop :=
  FittedContrastW4 ∧ FiniteImputationW4 ∧ PopulationLinearCEFW4.{u} ∧ CorrectedExampleW4

end
end SAP.P001e
