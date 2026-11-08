import Mathlib
import SAP.P001f.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001f

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
universe u

/-- The displayed augmented score, with the stable-outcomes censoring convention. -/
def augmentedMissingScore (y r m q : ℝ) : ℝ :=
  m + r * (censoredOutcome y r - m) / q

/-- P001-T113, Theorem 6.2.9, pp. 229–230 (PDF pp. 247–248): under MAR,
the augmented missing-data score has the outcome mean if either the respondent
regression is correct and the candidate propensity is bounded away from zero
and one, or the propensity is correct. The outcome and the complete displayed
score have finite expectations. No separate population integrability of the
nuisance regression is assumed. Conditional means, correctness, binarity and
overlap are interpreted as versions up to null sets; both response values have
positive probability. -/
def T113WholeStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y R : Ω → ℝ),
    Measurable Y → Measurable R → Integrable Y μ →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < (μ {ω | R ω = 0}).toReal → 0 < (μ {ω | R ω = 1}).toReal →
    ∀ p : (Fin K → ℝ) → ℝ, ConditionalMean μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    ConditionallyIndependent μ X hX Y R →
    ∀ m q : (Fin K → ℝ) → ℝ, Measurable m → Measurable q →
    Integrable (fun ω => augmentedMissingScore (Y ω) (R ω) (m (X ω)) (q (X ω))) μ →
    ((ConditionalMean (μ.restrict {ω | R ω = 1}) X
        (fun ω => censoredOutcome (Y ω) (R ω)) m ∧
        ∃ η : ℝ, 0 < η ∧ ∀ᵐ ω ∂μ, η < q (X ω) ∧ q (X ω) < 1 - η) ∨
      q ∘ X =ᵐ[μ] p ∘ X) →
    (∫ ω, Y ω ∂μ) =
      ∫ ω, augmentedMissingScore (Y ω) (R ω) (m (X ω)) (q (X ω)) ∂μ

/-- Retain treated observations and impute z for missing treated potential outcomes. -/
def imputedPotentialOne (y d z : ℝ) : ℝ := y * d + z * (1 - d)

/-- Retain control observations and impute z for missing control potential outcomes. -/
def imputedPotentialZero (y d z : ℝ) : ℝ := y * (1 - d) + z * d

/-- The individual imputation interpretation of the ATE bounds. Each observed
potential outcome is retained, each unobserved one is replaced by the selected
endpoint, and differencing the opposite endpoint imputations gives lowerATE
and upperATE. -/
def ATEIndividualImputations : Prop :=
  ∀ y0 y1 d a b : ℝ, y0 ∈ Set.Icc a b → y1 ∈ Set.Icc a b → (d = 0 ∨ d = 1) →
    let y := realizedOutcome y0 y1 d
    (d = 1 → ∀ z : ℝ,
      imputedPotentialOne y d z = y1 ∧ imputedPotentialZero y d z = z) ∧
    (d = 0 → ∀ z : ℝ,
      imputedPotentialOne y d z = z ∧ imputedPotentialZero y d z = y0) ∧
    y1 ∈ Set.Icc (imputedPotentialOne y d a) (imputedPotentialOne y d b) ∧
    y0 ∈ Set.Icc (imputedPotentialZero y d a) (imputedPotentialZero y d b) ∧
    imputedPotentialOne y d a - imputedPotentialZero y d b = lowerATE y d a b ∧
    imputedPotentialOne y d b - imputedPotentialZero y d a = upperATE y d a b

/-- P001-T114, Theorem 7.1.7 and its width and sharpness discussion,
pp. 241–244 (PDF pp. 259–262), and Example 7.1.6, p. 240 (PDF p. 258):
bounded potential outcomes and binary treatment with both arms of positive
probability give the printed conditional-arm ATE interval, of width b-a.
Every value in it is attained by bounded potential outcomes with the same
observable joint law. Individual endpoint imputations retain observed values
and bound the missing potential outcomes. For the six specified units, the
upper treated, lower control, lower treated and upper control mean estimates
are respectively 5/6, 1/6, 3/6 and 5/6, giving ATE endpoints -2/6 and 4/6. -/
def T114WholeStatement : Prop :=
  SharpATEBounds.{u} ∧ ATEIndividualImputations ∧
  ((∑ i : Fin 6, imputedPotentialOne (exampleOutcome i) (exampleIndicator i) 1) / 6 = 5 / 6 ∧
    (∑ i : Fin 6, imputedPotentialZero (exampleOutcome i) (exampleIndicator i) 0) / 6 = 1 / 6 ∧
    (∑ i : Fin 6, imputedPotentialOne (exampleOutcome i) (exampleIndicator i) 0) / 6 = 3 / 6 ∧
    (∑ i : Fin 6, imputedPotentialZero (exampleOutcome i) (exampleIndicator i) 1) / 6 = 5 / 6) ∧
  ((∑ i : Fin 6, lowerATE (exampleOutcome i) (exampleIndicator i) 0 1) / 6 = -2 / 6 ∧
    (∑ i : Fin 6, upperATE (exampleOutcome i) (exampleIndicator i) 0 1) / 6 = 4 / 6) ∧
  ((5 / 6 : ℝ) - 1 / 6 = 4 / 6 ∧ (3 / 6 : ℝ) - 5 / 6 = -2 / 6)

end
end SAP.P001f
