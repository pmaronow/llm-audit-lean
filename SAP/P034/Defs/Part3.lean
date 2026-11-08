import Mathlib
import SAP.P034.Defs.Part1
import SAP.P034.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P034

open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- `0/1` treatment coding in real-valued regressions; validator §2. -/
def bitR (b : Bool) : ℝ := if b then 1 else 0

/-- The full potential-variable bundle in the correction's randomization
condition H1 (fixed target T2; validator §2). -/
def potentialBundle {Ω : Type*} {k : ℕ} (M : SurveyModel Ω ℝ k) (ω : Ω) :
    ℝ × ℝ × Bool × Bool × (Fin k → ℝ) :=
  (M.Y false ω, M.Y true ω, M.R false ω, M.R true ω, M.X ω)

/-- `(Y(0),Y(1),X)` in the separate identifying condition H2:
“completion under each treatment is independent of potential outcomes and
pretreatment covariates” (corrected Study 2 PAP §8, target T2). -/
def outcomeCovariateBundle {Ω : Type*} {k : ℕ} (M : SurveyModel Ω ℝ k) (ω : Ω) :
    ℝ × ℝ × (Fin k → ℝ) := (M.Y false ω, M.Y true ω, M.X ω)

/-- The complete-case event `R=1`, where `R=R(T)` (validator §2). -/
def completedEvent {Ω K : Type*} {k : ℕ} (M : SurveyModel Ω K k) : Set Ω :=
  {ω | realizedCompletion M ω = true}

/-- The complete-case arm event `{T=t,R=1}` in correction T2(a)-(c). -/
def completedArm {Ω K : Type*} {k : ℕ} (M : SurveyModel Ω K k) (t : Bool) : Set Ω :=
  {ω | M.T ω = t ∧ realizedCompletion M ω = true}

/-- Ordinary conditioning on an event of positive probability, represented
by the normalized restriction measure (validator §2 and fixed target T2). -/
noncomputable def eventMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) : Measure Ω := (μ E)⁻¹ • μ.restrict E

/-- `E[f | E] = (∫_E f dP)/P(E)`, ordinary event conditional expectation
(fixed target T2, definitions_needed). Positivity is a theorem conclusion. -/
noncomputable def eventMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (f : Ω → ℝ) : ℝ :=
  (∫ ω in E, f ω ∂μ) / μ.real E

/-- Ordinary conditional event probability `P(A | E)`, correction T2(a). -/
noncomputable def eventProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A E : Set Ω) : ℝ := μ.real (A ∩ E) / μ.real E

/-- The target `τ=E[Y(1)-Y(0)]` in the general probability-space correction
(validator §2 and fixed target T2). -/
noncomputable def populationEffect {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (M : SurveyModel Ω ℝ k) : ℝ :=
  ∫ ω, M.Y true ω - M.Y false ω ∂μ

/-- The intercept, treatment, and `k` covariate indices of `Z=(1,T,X')'`
(fixed target T2(d)); the sum type explicitly separates the first two columns. -/
abbrev RegressionIndex (k : ℕ) := Fin 2 ⊕ Fin k

/-- `Z=(1,T,X')'` (validator §4; correction T2(d)) on a general sample space. -/
def populationDesign {Ω : Type*} {k : ℕ} (M : SurveyModel Ω ℝ k) (ω : Ω) :
    RegressionIndex k → ℝ :=
  Sum.elim (fun i => if i = 0 then 1 else bitR (M.T ω)) (M.X ω)

/-- `G=E[ZZ' | R=1]` (correction T2(d)), with entries given by event integrals. -/
noncomputable def populationGram {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (M : SurveyModel Ω ℝ k) :
    Matrix (RegressionIndex k) (RegressionIndex k) ℝ := fun i j =>
  eventMean μ (completedEvent M) (fun ω => populationDesign M ω i * populationDesign M ω j)

/-- `h=E[ZY | R=1]` (correction T2(d)). -/
noncomputable def populationRhs {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (M : SurveyModel Ω ℝ k) : RegressionIndex k → ℝ := fun i =>
  eventMean μ (completedEvent M) (fun ω => populationDesign M ω i * realizedOutcome M ω)

/-- “p=P(T=1 | R=1)” (correction T2(a)). -/
noncomputable def respondentTreatmentProbability {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (M : SurveyModel Ω ℝ k) : ℝ :=
  eventProbability μ {ω | M.T ω = true} (completedEvent M)

/-- All identification conclusions T2(a)-(d), without restricting the
sample space to be finite: positive arm response probabilities, respondent
treatment overlap, arm means, complete-case contrast, covariate laws,
orthogonality, all normal-equation solutions' treatment coefficient, and
unique existence when `G` is nonsingular. -/
def CompleteCaseIdentification {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (M : SurveyModel Ω ℝ k) : Prop :=
  (∀ t : Bool, μ.real (completedArm M t) =
    μ.real {ω | M.T ω = t} * μ.real {ω | M.R t ω = true} ∧
    0 < μ.real (completedArm M t)) ∧
  (0 < respondentTreatmentProbability μ M ∧ respondentTreatmentProbability μ M < 1) ∧
  (∀ t : Bool, eventMean μ (completedArm M t) (realizedOutcome M) = ∫ ω, M.Y t ω ∂μ) ∧
  (eventMean μ (completedArm M true) (realizedOutcome M) -
    eventMean μ (completedArm M false) (realizedOutcome M) = populationEffect μ M) ∧
  (∀ t : Bool, (eventMeasure μ (completedArm M t)).map M.X = μ.map M.X) ∧
  (∀ j : Fin k, eventMean μ (completedEvent M)
    (fun ω => (bitR (M.T ω) - respondentTreatmentProbability μ M) * M.X ω j) = 0) ∧
  (∀ β : RegressionIndex k → ℝ,
    (populationGram μ M).mulVec β = populationRhs μ M →
    β (Sum.inl 1) = populationEffect μ M) ∧
  (IsUnit (populationGram μ M).det →
    ∃! β : RegressionIndex k → ℝ, (populationGram μ M).mulVec β = populationRhs μ M)

/-- The concrete failure of the deleted implication, correction T2(e).
World A has randomized treatment and equal completion rates, but R(0) is
independent of neither Y(0) alone nor the full (Y(0),Y(1),X) bundle; its
normal-equation solution has nonzero treatment coefficient despite τ=0.
All variables reuse the validator's construction in T1 (§§2-5). -/
def EqualCompletionFailure : Prop :=
  finiteIndependent worldAWeight worldAModel.T worldABundle ∧
  (∀ t : Bool, finiteCondProb worldAWeight
    (fun ω => realizedCompletion worldAModel ω = true) (fun ω => worldAModel.T ω = t) = 1/2) ∧
  ¬ finiteIndependent worldAWeight (worldAModel.R false) (fun ω => ω 0) ∧
  ¬ finiteIndependent worldAWeight (worldAModel.R false) (fun ω => (ω 0, ω 0, ω 3)) ∧
  worldAEffect = 0 ∧ worldAGram.mulVec witnessBeta = worldARhs ∧
  witnessBeta 1 = 12/25 ∧ witnessBeta 1 ≠ worldAEffect

/-- P034-T2(a)-(e): randomization and the stated independent, positive
completion condition identify complete-case means and the OLS treatment
coefficient; equal completion rates alone fail in the fixed counterexample. -/
def T2Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ {k : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (M : SurveyModel Ω ℝ k),
    Measurable M.T → (∀ t, Measurable (M.Y t)) →
    (∀ t, Measurable (M.R t)) → Measurable M.X →
    (∀ t, MemLp (M.Y t) 2 μ) → MemLp M.X 2 μ →
    IndepFun M.T (potentialBundle M) μ →
    (0 < μ.real {ω | M.T ω = true} ∧ μ.real {ω | M.T ω = true} < 1) →
    (∀ t : Bool, IndepFun (M.R t) (outcomeCovariateBundle M) μ ∧
      0 < μ.real {ω | M.R t ω = true}) →
    CompleteCaseIdentification μ M ∧ EqualCompletionFailure

end SAP.P034
