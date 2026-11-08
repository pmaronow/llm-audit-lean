import Mathlib
import SAP.P034.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P034

open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- “Z=(1,T,X)'” (validator §4), for the one-covariate witness. -/
def worldADesign (ω : WorldA) : Fin 3 → ℚ :=
  ![1, bitQ (worldAModel.T ω), worldAModel.X ω 0]

/-- “G=E[ZZ' | R=1]” (validator §4), computed from the entire joint law. -/
def worldAGram : Matrix (Fin 3) (Fin 3) ℚ := fun i j =>
  finiteCondMean worldAWeight (fun ω => worldADesign ω i * worldADesign ω j)
    (fun ω => realizedCompletion worldAModel ω = true)

/-- “h=E[ZY | R=1]” (validator §4), computed from the entire joint law. -/
def worldARhs : Fin 3 → ℚ := fun i =>
  finiteCondMean worldAWeight (fun ω => worldADesign ω i * realizedOutcome worldAModel ω)
    (fun ω => realizedCompletion worldAModel ω = true)

/-- The matrix printed in fixed target T1(vii), validator §4. -/
def witnessGram : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1/2, 1/2; 1/2, 1/2, 1/4; 1/2, 1/4, 1/2]

/-- The right-hand side `(1/2,37/100,1/4)'` in T1(vii), validator §4. -/
def witnessRhs : Fin 3 → ℚ := ![1/2, 37/100, 1/4]

/-- The coefficient vector `(13/50,12/25,0)'` in T1(vii), validator §§4-5. -/
def witnessBeta : Fin 3 → ℚ := ![13/50, 12/25, 0]

/-- All finite numerical claims of T1(i)-(vii), including strict positivity
of every point mass and of every conditioning event. The binary bundle in
the independence assertion represents the actual potential variables. -/
def WorldANumericalFacts : Prop :=
  (∑ ω, worldAWeight ω) = 1 ∧ (∀ ω, 0 < worldAWeight ω) ∧
  finiteIndependent worldAWeight worldAModel.T worldABundle ∧
  finiteProb worldAWeight (fun ω => worldAModel.T ω = true) = 1/2 ∧
  (∀ ω, worldAModel.Y true ω - worldAModel.Y false ω = 0) ∧ worldAEffect = 0 ∧
  (∀ t : Bool, finiteCondProb worldAWeight
    (fun ω => realizedCompletion worldAModel ω = true) (fun ω => worldAModel.T ω = t) = 1/2) ∧
  (∀ t x y : Bool, 0 < finiteProb worldAWeight (worldAStratum t x y)) ∧
  (∀ t x y : Bool, finiteCondProb worldAWeight
    (fun ω => realizedCompletion worldAModel ω = true) (worldAStratum t x y) = completionChance t y) ∧
  (∀ t x : Bool, ¬ finiteConditionalIndependent worldAWeight
    (realizedCompletion worldAModel) (fun ω => ω 0)
    (fun ω => worldAModel.T ω = t ∧ ω 3 = x)) ∧
  ¬ finiteIndependent worldAWeight (worldAModel.R false) (fun ω => ω 0) ∧
  (∀ t : Bool, 0 < finiteProb worldAWeight
    (fun ω => worldAModel.T ω = t ∧ realizedCompletion worldAModel ω = true)) ∧
  worldAArmMean false = 13/50 ∧ worldAArmMean true = 37/50 ∧
  worldAArmMean true - worldAArmMean false = 12/25 ∧
  worldAArmMean true - worldAArmMean false ≠ worldAEffect ∧
  worldAGram = witnessGram ∧ worldARhs = witnessRhs ∧
  witnessGram.det = 1/16 ∧ witnessGram.mulVec witnessBeta = witnessRhs ∧
  witnessBeta 1 = 12/25 ∧ witnessBeta 1 ≠ worldAEffect

/-- Observed data consist of treatment, covariate, and either a missing
outcome (`none`) or a binary observed outcome (`some y`), validator §6. -/
abbrev ObservedCell := Bool × Bool × Option Bool

/-- The observed-data map in world A (validator §6). -/
def observedA (ω : WorldA) : ObservedCell :=
  (ω 4, ω 3, if realizedCompletion worldAModel ω then some (ω 0) else none)

/-- T1(viii)'s 400-unit data set as integer cell multiplicities: per `(t,x)`,
50 missing, and 50 observed split 37/13 or 13/37. Validator §5. This
frequency representation is exactly the finite data set, without an ordering. -/
def sampleCount (c : ObservedCell) : ℕ :=
  match c.2.2 with
  | none => 50
  | some y => if c.1 = y then 37 else 13

/-- The sample's `T`-by-`R` count table (validator §5). -/
def sampleCompletionCount (t r : Bool) : ℚ :=
  ∑ c : ObservedCell, if c.1 = t ∧ c.2.2.isSome = r then (sampleCount c : ℚ) else 0

/-- Pearson's expected count `(row total * column total)/N`, fixed target
T1(viii), where the row and column totals are computed from the count table. -/
def sampleExpectedCount (t r : Bool) : ℚ :=
  ((∑ s : Bool, sampleCompletionCount t s) *
    (∑ s : Bool, sampleCompletionCount s r)) / (∑ c : ObservedCell, (sampleCount c : ℚ))

/-- “Pearson's statistic ... equals 0” (validator §5): the usual sum of
`(observed-expected)^2/expected` over the four cells. -/
def samplePearson : ℚ := ∑ t : Bool, ∑ r : Bool,
  (sampleCompletionCount t r - sampleExpectedCount t r)^2 / sampleExpectedCount t r

/-- The upper-tail χ²₁ p-value is `P(Z² ≥ s)` for a standard Gaussian `Z`;
this is the exact definition of the reference distribution in T1(viii). -/
noncomputable def chiSquareOnePValue (s : ℝ) : ℝ :=
  ((gaussianReal 0 1) {z : ℝ | s ≤ z^2}).toReal

/-- “Z=(1,T,X)'” for an observed cell of the sample (validator §4-5). -/
def cellDesign (c : ObservedCell) : Fin 3 → ℚ := ![1, bitQ c.1, bitQ c.2.1]

/-- The sample OLS Gram matrix is the design cross-product over completed
records (validator §5); multiplicities implement repeated observations. -/
def sampleGram : Matrix (Fin 3) (Fin 3) ℚ := fun i j =>
  ∑ c : ObservedCell, if c.2.2.isSome then
    (sampleCount c : ℚ) * cellDesign c i * cellDesign c j else 0

/-- The sample OLS right-hand side, restricted to completed outcomes
(validator §5). `none` is skipped, not imputed. -/
def sampleRhs : Fin 3 → ℚ := fun i =>
  ∑ c : ObservedCell, match c.2.2 with
  | none => 0
  | some y => (sampleCount c : ℚ) * cellDesign c i * bitQ y

/-- The numerical assertions in T1(viii), with every observed-data cell of
the data set having positive population probability. -/
def SampleNumericalFacts : Prop :=
  (∑ c : ObservedCell, sampleCount c) = 400 ∧
  (∑ c : ObservedCell, if c.2.2.isSome then sampleCount c else 0) = 200 ∧
  (∀ t x : Bool, sampleCount (t,x,none) = 50) ∧
  (∀ x : Bool, sampleCount (false,x,some true) = 13 ∧
    sampleCount (false,x,some false) = 37 ∧ sampleCount (true,x,some true) = 37 ∧
    sampleCount (true,x,some false) = 13) ∧
  (∀ c : ObservedCell, 0 < finiteProb worldAWeight (fun ω => observedA ω = c)) ∧
  (∀ t r : Bool, sampleCompletionCount t r = 100 ∧ sampleExpectedCount t r = 100) ∧
  samplePearson = 0 ∧
  sampleGram = (200 : ℚ) • witnessGram ∧ sampleRhs = (200 : ℚ) • witnessRhs

/-- `Ω_B={0,1}^6`, coordinates `(y₀,y₁,r₀,r₁,x,t)` (validator §6). -/
abbrev WorldB := Fin 6 → Bool

/-- World B's product distribution, with outcome probabilities `13/50`
and `37/50` and four independent fair binary coordinates (validator §6). -/
def worldBWeight (ω : WorldB) : ℚ :=
  bernoulliMass (13/50) (ω 0) * bernoulliMass (37/50) (ω 1) * (1/16)

/-- The potential variables and realization in world B (validator §6);
this reuses `SurveyModel` and the realized-variable definitions from world A. -/
def worldBModel : SurveyModel WorldB ℚ 1 where
  T ω := ω 5
  Y t ω := bitQ (if t then ω 1 else ω 0)
  R t ω := if t then ω 3 else ω 2
  X ω _ := bitQ (ω 4)

/-- The observable triple in world B, with missing outcomes represented by
`none`, exactly as in world A (validator §6). -/
def observedB (ω : WorldB) : ObservedCell :=
  (ω 5, ω 4, if realizedCompletion worldBModel ω then
    some (if ω 5 then ω 1 else ω 0) else none)

/-- T1(ix): normalized positive world B, randomized treatment, completion
independent of all potential outcomes/covariates/treatment, effect `12/25`,
and equality of every observed-data cell probability with world A. -/
def WorldBFacts : Prop :=
  (∑ ω, worldBWeight ω) = 1 ∧ (∀ ω, 0 < worldBWeight ω) ∧
  finiteIndependent worldBWeight worldBModel.T
    (fun ω => (ω 0, ω 1, ω 2, ω 3, ω 4)) ∧
  finiteProb worldBWeight (fun ω => worldBModel.T ω = true) = 1/2 ∧
  finiteIndependent worldBWeight (fun ω => (ω 2, ω 3))
    (fun ω => (ω 0, ω 1, ω 4, ω 5)) ∧
  finiteMean worldBWeight (fun ω => worldBModel.Y true ω - worldBModel.Y false ω) = 12/25 ∧
  (∀ c : ObservedCell,
    finiteProb worldAWeight (fun ω => observedA ω = c) =
    finiteProb worldBWeight (fun ω => observedB ω = c)) ∧
  (∀ t x : Bool, finiteProb worldAWeight (fun ω => observedA ω = (t,x,none)) = 1/8) ∧
  (∀ x : Bool,
    finiteProb worldAWeight (fun ω => observedA ω = (false,x,some true)) = 13/400 ∧
    finiteProb worldAWeight (fun ω => observedA ω = (false,x,some false)) = 37/400 ∧
    finiteProb worldAWeight (fun ω => observedA ω = (true,x,some true)) = 37/400 ∧
    finiteProb worldAWeight (fun ω => observedA ω = (true,x,some false)) = 13/400)

/-- The respondent-population normal equations over real coefficients,
with the exact rational moments embedded in the real numbers. -/
noncomputable def realWitnessGram : Matrix (Fin 3) (Fin 3) ℝ :=
  witnessGram.map (fun q => (q : ℝ))

noncomputable def realWitnessRhs : Fin 3 → ℝ := fun i => (witnessRhs i : ℝ)

noncomputable def realWitnessBeta : Fin 3 → ℝ := fun i => (witnessBeta i : ℝ)

/-- The completed-sample cross-products over real coefficients. -/
noncomputable def realSampleGram : Matrix (Fin 3) (Fin 3) ℝ :=
  sampleGram.map (fun q => (q : ℝ))

noncomputable def realSampleRhs : Fin 3 → ℝ := fun i => (sampleRhs i : ℝ)

/-- P034-T1(i)-(ix): the finite counterexample, both unique real OLS fits,
the nonrejecting sample, and the observationally equivalent mechanism. -/
def T1Statement : Prop :=
  WorldANumericalFacts ∧
  (∀ β : Fin 3 → ℝ, realWitnessGram.mulVec β = realWitnessRhs ↔ β = realWitnessBeta) ∧
  SampleNumericalFacts ∧
  (chiSquareOnePValue (samplePearson : ℝ) = 1 ∧
    ¬ chiSquareOnePValue (samplePearson : ℝ) < (5/100 : ℝ)) ∧
  (∀ β : Fin 3 → ℝ, realSampleGram.mulVec β = realSampleRhs ↔ β = realWitnessBeta) ∧
  WorldBFacts

end SAP.P034
