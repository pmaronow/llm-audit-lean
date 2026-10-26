import Mathlib

namespace AronowAudit.P034

open scoped BigOperators
open MeasureTheory ProbabilityTheory

set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-!
P034-T1: an explicit finite counterexample to the Study 2 PAP's
missingness rule (amended plan §8, PDF pp. 5-6; Appendix pp. 9 and 18).
P034-T2: the sufficient identifying condition in the correction.
Neither construction is a claim of actual bias in the survey estimates.
The paper has no formal potential-outcome definitions; the definitions below
specify the models for P034-T1–T2.
-/

/-- “Y=Y(T), R=R(T)”.
`T` is the treatment, `Y t` the potential outcome, `R t` the potential
completion indicator, and `X` a finite vector of pretreatment covariates.
The paper's “survey completion rates” (article p. 6) concern `R`. -/
structure SurveyModel (Ω K : Type*) (k : ℕ) where
  T : Ω → Bool
  Y : Bool → Ω → K
  R : Bool → Ω → Bool
  X : Ω → Fin k → K

/-- “Y=Y(T)”: the outcome under the realized assignment. -/
def realizedOutcome {Ω K : Type*} {k : ℕ} (M : SurveyModel Ω K k) (ω : Ω) : K :=
  M.Y (M.T ω) ω

/-- “R=R(T)”: an outcome is observed iff this indicator is true. -/
def realizedCompletion {Ω K : Type*} {k : ℕ} (M : SurveyModel Ω K k) (ω : Ω) : Bool :=
  M.R (M.T ω) ω

/-- The numerical 0/1 coding used for treatment and binary outcomes in the
constructed witness. -/
def bitQ (b : Bool) : ℚ := if b then 1 else 0

/-- The finite probability of an event is the sum of its point masses.
All weights here are exact rationals. -/
def finiteProb {Ω : Type*} [Fintype Ω] (w : Ω → ℚ)
    (E : Ω → Prop) [DecidablePred E] : ℚ := ∑ ω, if E ω then w ω else 0

/-- “E[Y(1)-Y(0)]”, evaluated as a weighted finite sum. -/
def finiteMean {Ω : Type*} [Fintype Ω] (w : Ω → ℚ) (f : Ω → ℚ) : ℚ :=
  ∑ ω, w ω * f ω

/-- Ordinary event conditioning: the joint probability divided by the
conditioning event's probability. Positivity is checked
separately for every conditioning event used in the witness. -/
def finiteCondProb {Ω : Type*} [Fintype Ω] (w : Ω → ℚ)
    (E F : Ω → Prop) [DecidablePred E] [DecidablePred F] : ℚ :=
  finiteProb w (fun ω => E ω ∧ F ω) / finiteProb w F

/-- “E[Y | T=t,R=1]” and “E[ZZ' | R=1]”, with event
conditioning implemented by the normalized weighted finite sum. -/
def finiteCondMean {Ω : Type*} [Fintype Ω] (w : Ω → ℚ) (f : Ω → ℚ)
    (E : Ω → Prop) [DecidablePred E] : ℚ :=
  (∑ ω, if E ω then w ω * f ω else 0) / finiteProb w E

/-- Independence for finite-valued variables is the factorization of every
joint cell probability. -/
def finiteIndependent {Ω A B : Type*} [Fintype Ω] [DecidableEq A] [DecidableEq B]
    (w : Ω → ℚ) (f : Ω → A) (g : Ω → B) : Prop :=
  ∀ a b, finiteProb w (fun ω => f ω = a ∧ g ω = b) =
    finiteProb w (fun ω => f ω = a) * finiteProb w (fun ω => g ω = b)

/-- Independence within an event of positive probability, expressed as
factorization of every finite joint cell. -/
def finiteConditionalIndependent {Ω A B : Type*} [Fintype Ω]
    [DecidableEq A] [DecidableEq B] (w : Ω → ℚ) (f : Ω → A) (g : Ω → B)
    (E : Ω → Prop) [DecidablePred E] : Prop :=
  ∀ a b, finiteCondProb w (fun ω => f ω = a ∧ g ω = b) E =
    finiteCondProb w (fun ω => f ω = a) E * finiteCondProb w (fun ω => g ω = b) E

/-- `Ω={0,1}^5`, with coordinates `(u,r₀,r₁,x,t)` in P034-T1.
Booleans represent binary values without extra support hypotheses. -/
abbrev WorldA := Fin 5 → Bool

/-- `p₀(0)=37/50, p₀(1)=13/50, p₁(0)=13/50, p₁(1)=37/50`. -/
def completionChance (t u : Bool) : ℚ := if t = u then 37/50 else 13/50

/-- `p^r (1-p)^(1-r)` for a binary indicator. -/
def bernoulliMass (p : ℚ) (r : Bool) : ℚ := if r then p else 1-p

/-- `P(u,r₀,r₁,x,t)=1/8 p₀(u)^r₀(1-p₀(u))^(1-r₀)
p₁(u)^r₁(1-p₁(u))^(1-r₁)`. -/
def worldAWeight (ω : WorldA) : ℚ :=
  (1/8) * bernoulliMass (completionChance false (ω 0)) (ω 1) *
    bernoulliMass (completionChance true (ω 0)) (ω 2)

/-- “Y(0)=Y(1)=U” and the potential completions/covariate/assignment; the single binary covariate is also encoded as a rational. -/
def worldAModel : SurveyModel WorldA ℚ 1 where
  T ω := ω 4
  Y _ ω := bitQ (ω 0)
  R t ω := if t then ω 2 else ω 1
  X ω _ := bitQ (ω 3)

/-- `(Y(0),Y(1),R(0),R(1),X)` in its binary coding.
Both potential outcomes use the same `u`. -/
def worldABundle (ω : WorldA) : Bool × Bool × Bool × Bool × Bool :=
  (ω 0, ω 0, ω 1, ω 2, ω 3)

/-- The target “τ=E[Y(1)-Y(0)]”, for the constructed world A. -/
def worldAEffect : ℚ := finiteMean worldAWeight
  (fun ω => worldAModel.Y true ω - worldAModel.Y false ω)

/-- “E[Y | T=t,R=1]”, the complete-case arm mean. -/
def worldAArmMean (t : Bool) : ℚ := finiteCondMean worldAWeight
  (realizedOutcome worldAModel)
  (fun ω => worldAModel.T ω = t ∧ realizedCompletion worldAModel ω = true)

/-- The conditioning stratum `(T=t,X=x,Y=y)` in T1(v). -/
def worldAStratum (t x y : Bool) (ω : WorldA) : Prop :=
  worldAModel.T ω = t ∧ worldAModel.X ω 0 = bitQ x ∧
    realizedOutcome worldAModel ω = bitQ y

instance (t x y : Bool) : DecidablePred (worldAStratum t x y) :=
  fun ω => by unfold worldAStratum; infer_instance

/-- “Z=(1,T,X)'”, for the one-covariate witness. -/
def worldADesign (ω : WorldA) : Fin 3 → ℚ :=
  ![1, bitQ (worldAModel.T ω), worldAModel.X ω 0]

/-- “G=E[ZZ' | R=1]”, computed from the entire joint law. -/
def worldAGram : Matrix (Fin 3) (Fin 3) ℚ := fun i j =>
  finiteCondMean worldAWeight (fun ω => worldADesign ω i * worldADesign ω j)
    (fun ω => realizedCompletion worldAModel ω = true)

/-- “h=E[ZY | R=1]”, computed from the entire joint law. -/
def worldARhs : Fin 3 → ℚ := fun i =>
  finiteCondMean worldAWeight (fun ω => worldADesign ω i * realizedOutcome worldAModel ω)
    (fun ω => realizedCompletion worldAModel ω = true)

/-- The matrix printed in target T1(vii). -/
def witnessGram : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1/2, 1/2; 1/2, 1/2, 1/4; 1/2, 1/4, 1/2]

/-- The right-hand side `(1/2,37/100,1/4)'` in T1(vii). -/
def witnessRhs : Fin 3 → ℚ := ![1/2, 37/100, 1/4]

/-- The coefficient vector `(13/50,12/25,0)'` in T1(vii). -/
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

/-- T1(i)-(vii): exact enumeration of the 32-point witness verifies all
normalizations, randomization, outcome dependence, means and OLS moments. -/
theorem worldA_numerical_facts : WorldANumericalFacts := by
  unfold WorldANumericalFacts finiteIndependent finiteConditionalIndependent
  decide +kernel

/-- T1(vii): the displayed normal equations have exactly one solution,
namely `(13/50,12/25,0)'`; no statistical identification is assumed here. -/
theorem witness_normal_equations (β : Fin 3 → ℚ) :
    witnessGram.mulVec β = witnessRhs ↔ β = witnessBeta := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    norm_num [witnessGram, witnessRhs, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      at h0 h1 h2
    funext i
    fin_cases i <;> norm_num [witnessBeta] <;> linarith
  · rintro rfl
    decide +kernel

/-- Observed data consist of treatment, covariate, and either a missing
outcome (`none`) or a binary observed outcome (`some y`). -/
abbrev ObservedCell := Bool × Bool × Option Bool

/-- The observed-data map in world A. -/
def observedA (ω : WorldA) : ObservedCell :=
  (ω 4, ω 3, if realizedCompletion worldAModel ω then some (ω 0) else none)

/-- T1(viii)'s 400-unit data set as integer cell multiplicities: per `(t,x)`,
50 missing, and 50 observed split 37/13 or 13/37. This
frequency representation is exactly the finite data set, without an ordering. -/
def sampleCount (c : ObservedCell) : ℕ :=
  match c.2.2 with
  | none => 50
  | some y => if c.1 = y then 37 else 13

/-- The sample's `T`-by-`R` count table. -/
def sampleCompletionCount (t r : Bool) : ℚ :=
  ∑ c : ObservedCell, if c.1 = t ∧ c.2.2.isSome = r then (sampleCount c : ℚ) else 0

/-- Pearson's expected count `(row total * column total)/N`, target
T1(viii), where the row and column totals are computed from the count table. -/
def sampleExpectedCount (t r : Bool) : ℚ :=
  ((∑ s : Bool, sampleCompletionCount t s) *
    (∑ s : Bool, sampleCompletionCount s r)) / (∑ c : ObservedCell, (sampleCount c : ℚ))

/-- “Pearson's statistic ... equals 0”: the usual sum of
`(observed-expected)^2/expected` over the four cells. -/
def samplePearson : ℚ := ∑ t : Bool, ∑ r : Bool,
  (sampleCompletionCount t r - sampleExpectedCount t r)^2 / sampleExpectedCount t r

/-- The upper-tail χ²₁ p-value is `P(Z² ≥ s)` for a standard Gaussian `Z`;
this is the exact definition of the reference distribution in T1(viii). -/
noncomputable def chiSquareOnePValue (s : ℝ) : ℝ :=
  ((gaussianReal 0 1) {z : ℝ | s ≤ z^2}).toReal

/-- “Z=(1,T,X)'” for an observed cell of the sample. -/
def cellDesign (c : ObservedCell) : Fin 3 → ℚ := ![1, bitQ c.1, bitQ c.2.1]

/-- The sample OLS Gram matrix is the design cross-product over completed
records; multiplicities implement repeated observations. -/
def sampleGram : Matrix (Fin 3) (Fin 3) ℚ := fun i j =>
  ∑ c : ObservedCell, if c.2.2.isSome then
    (sampleCount c : ℚ) * cellDesign c i * cellDesign c j else 0

/-- The sample OLS right-hand side, restricted to completed outcomes. `none` is skipped, not imputed. -/
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

/-- T1(viii): the 400-unit table, its Pearson statistic, and its sample
normal equations are verified from the integer cell counts. -/
theorem sample_numerical_facts : SampleNumericalFacts := by
  unfold SampleNumericalFacts
  decide +kernel

/-- T1(viii): a zero statistic has χ²₁ upper-tail probability one, hence
the stated sample does not reject at level 0.05. -/
theorem sample_test_nonrejection :
    chiSquareOnePValue (samplePearson : ℝ) = 1 ∧
      ¬ chiSquareOnePValue (samplePearson : ℝ) < (5/100 : ℝ) := by
  have hz : samplePearson = 0 := by decide +kernel
  have hs : {z : ℝ | (0 : ℝ) ≤ z^2} = Set.univ :=
    Set.eq_univ_of_forall (fun z => sq_nonneg z)
  have hp : chiSquareOnePValue 0 = 1 := by simp [chiSquareOnePValue, hs]
  norm_num [hz, hp]

/-- T1(viii): the normal equations on the 200 completed sample records
have the same unique solution as the respondent-population equations. -/
theorem sample_normal_equations (β : Fin 3 → ℚ) :
    sampleGram.mulVec β = sampleRhs ↔ β = witnessBeta := by
  have hg : sampleGram = (200 : ℚ) • witnessGram := by decide +kernel
  have hh : sampleRhs = (200 : ℚ) • witnessRhs := by decide +kernel
  rw [hg, hh, Matrix.smul_mulVec]
  have he : (200 : ℚ) • (witnessGram.mulVec β) = (200 : ℚ) • witnessRhs ↔
      witnessGram.mulVec β = witnessRhs := by
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      change 200 * (witnessGram.mulVec β i) = 200 * witnessRhs i at hi
      linarith
    · intro h; rw [h]
  exact he.trans (witness_normal_equations β)

/-- `Ω_B={0,1}^6`, coordinates `(y₀,y₁,r₀,r₁,x,t)`. -/
abbrev WorldB := Fin 6 → Bool

/-- World B's product distribution, with outcome probabilities `13/50`
and `37/50` and four independent fair binary coordinates. -/
def worldBWeight (ω : WorldB) : ℚ :=
  bernoulliMass (13/50) (ω 0) * bernoulliMass (37/50) (ω 1) * (1/16)

/-- The potential variables and realization in world B;
this reuses `SurveyModel` and the realized-variable definitions from world A. -/
def worldBModel : SurveyModel WorldB ℚ 1 where
  T ω := ω 5
  Y t ω := bitQ (if t then ω 1 else ω 0)
  R t ω := if t then ω 3 else ω 2
  X ω _ := bitQ (ω 4)

/-- The observable triple in world B, with missing outcomes represented by
`none`, exactly as in world A. -/
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

/-- T1(ix): exact enumeration proves observational equivalence with an
independent-completion world whose target effect is `12/25`. -/
theorem worldB_observational_equivalence : WorldBFacts := by
  unfold WorldBFacts finiteIndependent
  decide +kernel

/-- P034-T1 in full: claims (i)-(ix) for the concrete witness,
including unique population and sample OLS solutions and exact test
non-rejection. Amended Study 2 PAP §8 and Appendix Figures OA2a/OA3 notes.
Equal completion rates therefore do not justify the complete-case effect. -/
theorem missingness_counterexample :
    WorldANumericalFacts ∧
    (∀ β : Fin 3 → ℚ, witnessGram.mulVec β = witnessRhs ↔ β = witnessBeta) ∧
    SampleNumericalFacts ∧
    (chiSquareOnePValue (samplePearson : ℝ) = 1 ∧
      ¬ chiSquareOnePValue (samplePearson : ℝ) < (5/100 : ℝ)) ∧
    (∀ β : Fin 3 → ℚ, sampleGram.mulVec β = sampleRhs ↔ β = witnessBeta) ∧
    WorldBFacts := by
  exact ⟨worldA_numerical_facts, witness_normal_equations, sample_numerical_facts,
    sample_test_nonrejection, sample_normal_equations, worldB_observational_equivalence⟩

/-! General probability-space version of the correction P034-T2. -/

/-- `0/1` treatment coding in real-valued regressions. -/
def bitR (b : Bool) : ℝ := if b then 1 else 0

/-- The full potential-variable bundle in the correction's randomization
condition H1 (P034-T2). -/
def potentialBundle {Ω : Type*} {k : ℕ} (M : SurveyModel Ω ℝ k) (ω : Ω) :
    ℝ × ℝ × Bool × Bool × (Fin k → ℝ) :=
  (M.Y false ω, M.Y true ω, M.R false ω, M.R true ω, M.X ω)

/-- `(Y(0),Y(1),X)` in the separate identifying condition H2:
“completion under each treatment is independent of potential outcomes and
pretreatment covariates” (corrected Study 2 PAP §8, target T2). -/
def outcomeCovariateBundle {Ω : Type*} {k : ℕ} (M : SurveyModel Ω ℝ k) (ω : Ω) :
    ℝ × ℝ × (Fin k → ℝ) := (M.Y false ω, M.Y true ω, M.X ω)

/-- The complete-case event `R=1`, where `R=R(T)`. -/
def completedEvent {Ω K : Type*} {k : ℕ} (M : SurveyModel Ω K k) : Set Ω :=
  {ω | realizedCompletion M ω = true}

/-- The complete-case arm event `{T=t,R=1}` in correction T2(a)-(c). -/
def completedArm {Ω K : Type*} {k : ℕ} (M : SurveyModel Ω K k) (t : Bool) : Set Ω :=
  {ω | M.T ω = t ∧ realizedCompletion M ω = true}

/-- Ordinary conditioning on an event of positive probability, represented
by the normalized restriction measure (P034-T2). -/
noncomputable def eventMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) : Measure Ω := (μ E)⁻¹ • μ.restrict E

/-- `E[f | E] = (∫_E f dP)/P(E)`, ordinary event conditional expectation
in P034-T2. Positivity is a theorem conclusion. -/
noncomputable def eventMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (f : Ω → ℝ) : ℝ :=
  (∫ ω in E, f ω ∂μ) / μ.real E

/-- Ordinary conditional event probability `P(A | E)`, correction T2(a). -/
noncomputable def eventProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A E : Set Ω) : ℝ := μ.real (A ∩ E) / μ.real E

/-- The target `τ=E[Y(1)-Y(0)]` in the general probability-space correction
P034-T2. -/
noncomputable def populationEffect {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (M : SurveyModel Ω ℝ k) : ℝ :=
  ∫ ω, M.Y true ω - M.Y false ω ∂μ

/-- The intercept, treatment, and `k` covariate indices of `Z=(1,T,X')'`
(target T2(d)); the sum type explicitly separates the first two columns. -/
abbrev RegressionIndex (k : ℕ) := Fin 2 ⊕ Fin k

/-- `Z=(1,T,X')'` (correction T2(d)) on a general sample space. -/
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

/-- The distribution-preservation step underlying correction T2(b)-(c).
If assignment is independent of completion and a baseline variable jointly,
and completion is independent of that variable, the selected-arm law of
the baseline variable is its original law times the arm response probability.
This supporting lemma is general, rather than a finite-space restriction. -/
theorem selected_arm_unnormalized_law
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) (T R : Ω → Bool) (f : Ω → A)
    (_hT : Measurable T) (_hR : Measurable R) (hf : Measurable f)
    (h1 : IndepFun T (fun ω => (R ω, f ω)) μ) (h2 : IndepFun R f μ) (t : Bool) :
    (μ.restrict {ω | T ω = t ∧ R ω = true}).map f =
      (μ {ω | T ω = t} * μ {ω | R ω = true}) • μ.map f := by
  classical
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs, Measure.restrict_apply (hf hs), Measure.smul_apply,
    Measure.map_apply hf hs]
  have e1 := h1.measure_inter_preimage_eq_mul {t} ({true} ×ˢ s)
    (measurableSet_singleton t) ((measurableSet_singleton true).prod hs)
  have e2 := h2.measure_inter_preimage_eq_mul {true} s (measurableSet_singleton true) hs
  have hset : f ⁻¹' s ∩ {ω | T ω = t ∧ R ω = true} =
      T ⁻¹' {t} ∩ (fun ω => (R ω, f ω)) ⁻¹' ({true} ×ˢ s) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, Set.mem_prod]
    tauto
  have hrset : (fun ω => (R ω, f ω)) ⁻¹' ({true} ×ˢ s) = R ⁻¹' {true} ∩ f ⁻¹' s := by
    ext ω; rfl
  rw [hset, e1, hrset, e2]
  change μ (T ⁻¹' {t}) * (μ (R ⁻¹' {true}) * μ (f ⁻¹' s)) =
    (μ (T ⁻¹' {t}) * μ (R ⁻¹' {true})) * μ (f ⁻¹' s)
  exact (mul_assoc _ _ _).symm

/-- The normalized form of distribution preservation in correction
T2(b)-(c): positive independent completion within a randomized arm retains
the law of the baseline variable. Includes the exact arm-response mass. -/
theorem selected_arm_normalized_law
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T R : Ω → Bool) (f : Ω → A)
    (hT : Measurable T) (hR : Measurable R) (hf : Measurable f)
    (h1 : IndepFun T (fun ω => (R ω, f ω)) μ) (h2 : IndepFun R f μ)
    (t : Bool) (ht : 0 < μ.real {ω | T ω = t}) (hr : 0 < μ.real {ω | R ω = true}) :
    μ.real {ω | T ω = t ∧ R ω = true} =
      μ.real {ω | T ω = t} * μ.real {ω | R ω = true} ∧
    0 < μ.real {ω | T ω = t ∧ R ω = true} ∧
    (eventMeasure μ {ω | T ω = t ∧ R ω = true}).map f = μ.map f := by
  have hraw := selected_arm_unnormalized_law μ T R f hT hR hf h1 h2 t
  have hmass := congrArg (fun ν : Measure A => ν Set.univ) hraw
  simp only [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at hmass
  have hmreal : μ.real {ω | T ω = t ∧ R ω = true} =
      μ.real {ω | T ω = t} * μ.real {ω | R ω = true} := by
    simp only [measureReal_def, hmass, ENNReal.toReal_mul]
  have hpos : 0 < μ.real {ω | T ω = t ∧ R ω = true} := by
    rw [hmreal]; exact mul_pos ht hr
  refine ⟨hmreal, hpos, ?_⟩
  have hn : μ {ω | T ω = t ∧ R ω = true} ≠ 0 := by
    intro h; simp [measureReal_def, h] at hpos
  unfold eventMeasure
  rw [Measure.map_smul _ hf.aemeasurable, hraw, smul_smul, ← hmass,
    ENNReal.inv_mul_cancel hn (measure_ne_top μ _), one_smul]

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

/-- Correction T2(a) and the joint-law content behind (b)-(c), under H1
and H2 exactly. Selection in either arm preserves the full joint law of
both potential outcomes and covariates, and each arm response event has
strictly positive probability. No finiteness restriction on the space. -/
theorem potential_selected_laws
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : SurveyModel Ω ℝ k)
    (hT : Measurable M.T) (hY : ∀ t, Measurable (M.Y t))
    (hR : ∀ t, Measurable (M.R t)) (hX : Measurable M.X)
    (hH1 : IndepFun M.T (potentialBundle M) μ)
    (hOverlap : 0 < μ.real {ω | M.T ω = true} ∧ μ.real {ω | M.T ω = true} < 1)
    (hH2 : ∀ t : Bool, IndepFun (M.R t) (outcomeCovariateBundle M) μ ∧
      0 < μ.real {ω | M.R t ω = true}) :
    ∀ t : Bool, μ.real (completedArm M t) =
      μ.real {ω | M.T ω = t} * μ.real {ω | M.R t ω = true} ∧
      0 < μ.real (completedArm M t) ∧
      (eventMeasure μ (completedArm M t)).map (outcomeCovariateBundle M) =
        μ.map (outcomeCovariateBundle M) := by
  intro t
  have hf : Measurable (outcomeCovariateBundle M) :=
    (hY false).prodMk ((hY true).prodMk hX)
  let ψ : (ℝ × ℝ × Bool × Bool × (Fin k → ℝ)) → Bool × (ℝ × ℝ × (Fin k → ℝ)) :=
    fun v => (if t then v.2.2.2.1 else v.2.2.1, (v.1, v.2.1, v.2.2.2.2))
  have hψ : Measurable ψ := by
    cases t <;> dsimp [ψ] <;> fun_prop
  have hi : IndepFun M.T (fun ω => (M.R t ω, outcomeCovariateBundle M ω)) μ := by
    have h := hH1.comp measurable_id hψ
    cases t <;> simpa [ψ, potentialBundle, outcomeCovariateBundle, Function.comp_def] using h
  have ht : 0 < μ.real {ω | M.T ω = t} := by
    cases t
    · have hc : {ω | M.T ω = false} = {ω | M.T ω = true}ᶜ := by
        ext ω; cases h : M.T ω <;> simp [h]
      have hs : MeasurableSet {ω | M.T ω = true} := by
        simpa only [Set.preimage, Set.mem_singleton_iff] using hT (measurableSet_singleton true)
      rw [hc, measureReal_compl hs]
      simp only [probReal_univ]
      linarith [hOverlap.2]
    · exact hOverlap.1
  have he : completedArm M t = {ω | M.T ω = t ∧ M.R t ω = true} := by
    ext ω
    constructor
    · rintro ⟨ht, hr⟩
      exact ⟨ht, by simpa [realizedCompletion, ht] using hr⟩
    · rintro ⟨ht, hr⟩
      exact ⟨ht, by simpa [realizedCompletion, ht] using hr⟩
  rw [he]
  exact selected_arm_normalized_law μ M.T (M.R t) (outcomeCovariateBundle M)
    hT (hR t) hf hi (hH2 t).1 t ht (hH2 t).2

/-- The arm event `{T=t,R(T)=1}` equals `{T=t,R(t)=1}` by the
realization definition, target T2(a). -/
theorem completed_arm_eq {Ω K : Type*} {k : ℕ} (M : SurveyModel Ω K k) (t : Bool) :
    completedArm M t = {ω | M.T ω = t ∧ M.R t ω = true} := by
  ext ω
  constructor
  · rintro ⟨ht, hr⟩
    exact ⟨ht, by simpa [realizedCompletion, ht] using hr⟩
  · rintro ⟨ht, hr⟩
    exact ⟨ht, by simpa [realizedCompletion, ht] using hr⟩

/-- The events used in ordinary event conditioning in T2 are measurable
because treatment and potential completion are random variables. -/
theorem completed_arm_measurable {Ω K : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SurveyModel Ω K k) (hT : Measurable M.T)
    (hR : ∀ t, Measurable (M.R t)) (t : Bool) : MeasurableSet (completedArm M t) := by
  rw [completed_arm_eq]
  have h := (hT (measurableSet_singleton t)).inter (hR t (measurableSet_singleton true))
  convert h using 1
  ext ω
  simp

/-- Ordinary event expectation agrees with integration under the normalized
event measure, by the definitions in correction T2. -/
theorem event_mean_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (f : Ω → ℝ) :
    eventMean μ E f = ∫ ω, f ω ∂(eventMeasure μ E) := by
  simp [eventMean, eventMeasure, integral_smul_measure, measureReal_def,
    smul_eq_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]

/-- If event selection preserves a real variable's law, its conditional
mean equals its original mean (the measure-theoretic step of T2(b)). -/
theorem event_mean_of_preserved_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (f : Ω → ℝ) (hf : Measurable f)
    (hmap : (eventMeasure μ E).map f = μ.map f) : eventMean μ E f = ∫ ω, f ω ∂μ := by
  rw [event_mean_eq_integral]
  have h := congrArg (fun ν : Measure ℝ => ∫ y : ℝ, y ∂ν) hmap
  calc
    (∫ ω, f ω ∂eventMeasure μ E) = (∫ y : ℝ, y ∂(eventMeasure μ E).map f) :=
      (integral_map_of_stronglyMeasurable hf measurable_id.stronglyMeasurable).symm
    _ = (∫ y : ℝ, y ∂μ.map f) := h
    _ = (∫ ω, f ω ∂μ) := integral_map_of_stronglyMeasurable hf measurable_id.stronglyMeasurable

/-- Correction T2(b)-(c): randomized independent positive completion
preserves each arm's mean outcome and the pretreatment covariate law.
These are general probability-space conclusions, not finite approximations. -/
theorem corrected_arm_means_and_covariates
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : SurveyModel Ω ℝ k)
    (hT : Measurable M.T) (hY : ∀ t, Measurable (M.Y t))
    (hR : ∀ t, Measurable (M.R t)) (hX : Measurable M.X)
    (hH1 : IndepFun M.T (potentialBundle M) μ)
    (hOverlap : 0 < μ.real {ω | M.T ω = true} ∧ μ.real {ω | M.T ω = true} < 1)
    (hH2 : ∀ t : Bool, IndepFun (M.R t) (outcomeCovariateBundle M) μ ∧
      0 < μ.real {ω | M.R t ω = true}) :
    ∀ t : Bool, eventMean μ (completedArm M t) (realizedOutcome M) = ∫ ω, M.Y t ω ∂μ ∧
      (eventMeasure μ (completedArm M t)).map M.X = μ.map M.X := by
  intro t
  have hLaw := (potential_selected_laws μ M hT hY hR hX hH1 hOverlap hH2 t).2.2
  have hf : Measurable (outcomeCovariateBundle M) :=
    (hY false).prodMk ((hY true).prodMk hX)
  let π : (ℝ × ℝ × (Fin k → ℝ)) → ℝ := fun v => if t then v.2.1 else v.1
  have hπ : Measurable π := by cases t <;> dsimp [π] <;> fun_prop
  have hyMap : (eventMeasure μ (completedArm M t)).map (M.Y t) = μ.map (M.Y t) := by
    have hm := congrArg (fun ν : Measure (ℝ × ℝ × (Fin k → ℝ)) => ν.map π) hLaw
    rw [Measure.map_map hπ hf, Measure.map_map hπ hf] at hm
    cases t <;> simpa [π, outcomeCovariateBundle, Function.comp_def] using hm
  have hxMap : (eventMeasure μ (completedArm M t)).map M.X = μ.map M.X := by
    have hm := congrArg (fun ν : Measure (ℝ × ℝ × (Fin k → ℝ)) =>
      ν.map (fun v => v.2.2)) hLaw
    rw [Measure.map_map (by fun_prop) hf, Measure.map_map (by fun_prop) hf] at hm
    simpa [outcomeCovariateBundle, Function.comp_def] using hm
  refine ⟨?_, hxMap⟩
  have he : eventMean μ (completedArm M t) (realizedOutcome M) =
      eventMean μ (completedArm M t) (M.Y t) := by
    unfold eventMean
    congr 1
    apply setIntegral_congr_fun (completed_arm_measurable M hT hR t)
    intro ω hω
    simp [realizedOutcome, hω.1]
  rw [he]
  exact event_mean_of_preserved_law μ _ _ (hY t) hyMap

/-- Complete cases partition into the two disjoint treatment arms, as in
correction T2(a). This uses only the binary coding of the design. -/
theorem completed_event_union {Ω K : Type*} {k : ℕ} (M : SurveyModel Ω K k) :
    completedEvent M = completedArm M false ∪ completedArm M true := by
  ext ω
  cases ht : M.T ω <;> simp [completedEvent, completedArm, ht]

/-- The two completed treatment arms in T2 are disjoint. -/
theorem completed_arms_disjoint {Ω K : Type*} {k : ℕ} (M : SurveyModel Ω K k) :
    Disjoint (completedArm M false) (completedArm M true) := by
  apply Set.disjoint_left.mpr
  intro ω h0 h1
  have ht0 := h0.1
  have ht1 := h1.1
  rw [ht0] at ht1
  cases ht1

/-- The exact binary mixture identity behind correction T2(c)-(d):
respondent overlap follows from positive response in both arms, and every
integrable respondent variable averages its two arm means with weights
`1-p` and `p`. This is valid on general probability spaces. -/
theorem respondent_mixture {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : SurveyModel Ω ℝ k)
    (hT : Measurable M.T) (hR : ∀ t, Measurable (M.R t))
    (hq0 : 0 < μ.real (completedArm M false)) (hq1 : 0 < μ.real (completedArm M true)) :
    (0 < respondentTreatmentProbability μ M ∧ respondentTreatmentProbability μ M < 1) ∧
    ∀ f : Ω → ℝ, IntegrableOn f (completedEvent M) μ →
      eventMean μ (completedEvent M) f =
        (1-respondentTreatmentProbability μ M) * eventMean μ (completedArm M false) f +
          respondentTreatmentProbability μ M * eventMean μ (completedArm M true) f := by
  have hm0 := completed_arm_measurable M hT hR false
  have hm1 := completed_arm_measurable M hT hR true
  have hdis := completed_arms_disjoint M
  have hmass : μ.real (completedEvent M) =
      μ.real (completedArm M false) + μ.real (completedArm M true) := by
    rw [completed_event_union, measureReal_union hdis hm1]
  have hs : 0 < μ.real (completedArm M false) + μ.real (completedArm M true) := add_pos hq0 hq1
  have hp : respondentTreatmentProbability μ M =
      μ.real (completedArm M true) /
        (μ.real (completedArm M false) + μ.real (completedArm M true)) := by
    unfold respondentTreatmentProbability eventProbability
    have he : {ω | M.T ω = true} ∩ completedEvent M = completedArm M true := by
      ext ω; rfl
    rw [he, hmass]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hp]; exact div_pos hq1 hs
  · rw [hp, div_lt_one hs]; linarith
  · intro f hf
    have hf0 : IntegrableOn f (completedArm M false) μ :=
      hf.mono_set (by rw [completed_event_union]; exact Set.subset_union_left)
    have hf1 : IntegrableOn f (completedArm M true) μ :=
      hf.mono_set (by rw [completed_event_union]; exact Set.subset_union_right)
    have hi : (∫ ω in completedEvent M, f ω ∂μ) =
        (∫ ω in completedArm M false, f ω ∂μ) + (∫ ω in completedArm M true, f ω ∂μ) := by
      rw [completed_event_union, setIntegral_union hdis hm1 hf0 hf1]
    unfold eventMean
    rw [hi, hmass, hp]
    field_simp [ne_of_gt hq0, ne_of_gt hq1, ne_of_gt hs]
    ring

/-- Multiplication by the treatment indicator is multiplication by the
constant arm value within a completed arm (correction T2's finite algebra). -/
theorem arm_mean_treatment_mul {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (M : SurveyModel Ω ℝ k) (hT : Measurable M.T)
    (hR : ∀ t, Measurable (M.R t)) (t : Bool) (f : Ω → ℝ) :
    eventMean μ (completedArm M t) (fun ω => bitR (M.T ω)*f ω) =
      bitR t * eventMean μ (completedArm M t) f := by
  have he : (∫ ω in completedArm M t, bitR (M.T ω)*f ω ∂μ) =
      ∫ ω in completedArm M t, bitR t * f ω ∂μ := by
    apply setIntegral_congr_fun (completed_arm_measurable M hT hR t)
    intro ω hω
    change bitR (M.T ω)*f ω = bitR t*f ω
    rw [hω.1]
  unfold eventMean
  rw [he, integral_const_mul]
  ring

/-- Integrability is preserved by multiplication by a measurable binary
treatment indicator; this is the indicator form of the finite-moment
requirements in correction T2(d). -/
theorem integrable_treatment_mul {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (M : SurveyModel Ω ℝ k) (hT : Measurable M.T)
    (f : Ω → ℝ) (hf : Integrable f μ) : Integrable (fun ω => bitR (M.T ω)*f ω) μ := by
  classical
  have hs : MeasurableSet {ω | M.T ω = true} := by
    simpa only [Set.preimage, Set.mem_singleton_iff] using hT (measurableSet_singleton true)
  have hi := hf.indicator hs
  convert hi using 1
  ext ω
  cases ht : M.T ω <;> simp [bitR, ht]

/-- Ordinary event means of constants equal those constants when the
conditioning event has positive probability, as required in T2(a). -/
theorem event_mean_const {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hE : 0 < μ.real E) (c : ℝ) :
    eventMean μ E (fun _ => c) = c := by
  simp only [eventMean, setIntegral_const, smul_eq_mul]
  field_simp [ne_of_gt hE]

/-- Finite linearity step for the event expectations used in T2(c)-(d). -/
theorem event_mean_sub {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω)
    (f g : Ω → ℝ) (hf : IntegrableOn f E μ) (hg : IntegrableOn g E μ) :
    eventMean μ E (fun ω => f ω-g ω) = eventMean μ E f-eventMean μ E g := by
  unfold eventMean
  rw [integral_sub hf hg]
  ring

/-- Scalar linearity of event means used in correction T2(c)-(d). -/
theorem event_mean_const_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Set Ω) (c : ℝ) (f : Ω → ℝ) :
    eventMean μ E (fun ω => c*f ω) = c*eventMean μ E f := by
  unfold eventMean
  rw [integral_const_mul]
  ring

/-- The moment identities used to multiply the normal equations by
`(-p,1,0')` (target T2(d)). These are intermediate conclusions, not
additional identifying assumptions. -/
structure RespondentMomentIdentities {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (M : SurveyModel Ω ℝ k) : Prop where
  overlap : 0 < respondentTreatmentProbability μ M ∧ respondentTreatmentProbability μ M < 1
  oneMean : eventMean μ (completedEvent M) (fun _ => 1) = 1
  treatmentMean : eventMean μ (completedEvent M) (fun ω => bitR (M.T ω)) =
    respondentTreatmentProbability μ M
  treatmentSquareMean : eventMean μ (completedEvent M) (fun ω => bitR (M.T ω)^2) =
    respondentTreatmentProbability μ M
  covariateMean : ∀ j : Fin k, eventMean μ (completedEvent M) (fun ω => M.X ω j) =
    ∫ ω, M.X ω j ∂μ
  treatmentCovariateMean : ∀ j : Fin k, eventMean μ (completedEvent M)
    (fun ω => bitR (M.T ω)*M.X ω j) =
    respondentTreatmentProbability μ M * ∫ ω, M.X ω j ∂μ
  outcomeMean : eventMean μ (completedEvent M) (realizedOutcome M) =
    (1-respondentTreatmentProbability μ M)*(∫ ω, M.Y false ω ∂μ) +
      respondentTreatmentProbability μ M*(∫ ω, M.Y true ω ∂μ)
  treatmentOutcomeMean : eventMean μ (completedEvent M)
    (fun ω => bitR (M.T ω)*realizedOutcome M ω) =
    respondentTreatmentProbability μ M*(∫ ω, M.Y true ω ∂μ)
  covarianceZero : ∀ j : Fin k, eventMean μ (completedEvent M)
    (fun ω => (bitR (M.T ω)-respondentTreatmentProbability μ M)*M.X ω j) = 0
  effectContrast : populationEffect μ M = (∫ ω, M.Y true ω ∂μ)-(∫ ω, M.Y false ω ∂μ)

/-- The full respondent moment identities of correction T2(c)-(d) follow
from H1, H2 and finite second moments on a general probability space.
The arm laws come from `potential_selected_laws`; the remaining identities
are exact two-arm mixture calculations. -/
theorem corrected_respondent_moments
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : SurveyModel Ω ℝ k)
    (hT : Measurable M.T) (hY : ∀ t, Measurable (M.Y t))
    (hR : ∀ t, Measurable (M.R t)) (hX : Measurable M.X)
    (hY2 : ∀ t, MemLp (M.Y t) 2 μ) (hX2 : MemLp M.X 2 μ)
    (hH1 : IndepFun M.T (potentialBundle M) μ)
    (hOverlap : 0 < μ.real {ω | M.T ω = true} ∧ μ.real {ω | M.T ω = true} < 1)
    (hH2 : ∀ t : Bool, IndepFun (M.R t) (outcomeCovariateBundle M) μ ∧
      0 < μ.real {ω | M.R t ω = true}) : RespondentMomentIdentities μ M := by
  classical
  have hSel := potential_selected_laws μ M hT hY hR hX hH1 hOverlap hH2
  have hArm := corrected_arm_means_and_covariates μ M hT hY hR hX hH1 hOverlap hH2
  have hq : ∀ t, 0 < μ.real (completedArm M t) := fun t => (hSel t).2.1
  have hMixture := respondent_mixture μ M hT hR (hq false) (hq true)
  have hE : 0 < μ.real (completedEvent M) := by
    rw [completed_event_union, measureReal_union (completed_arms_disjoint M)
      (completed_arm_measurable M hT hR true)]
    exact add_pos (hq false) (hq true)
  have hyI : ∀ t, Integrable (M.Y t) μ := fun t => MemLp.integrable (by norm_num) (hY2 t)
  have hxI : ∀ j : Fin k, Integrable (fun ω => M.X ω j) μ :=
    fun j => MemLp.integrable (by norm_num) (hX2.eval j)
  have hsT : MeasurableSet {ω | M.T ω = true} := by
    simpa only [Set.preimage, Set.mem_singleton_iff] using hT (measurableSet_singleton true)
  have hyRealI : Integrable (realizedOutcome M) μ := by
    have hi := Integrable.piecewise hsT (hyI true).integrableOn (hyI false).integrableOn
    convert hi using 1
    ext ω
    cases ht : M.T ω <;> simp [realizedOutcome, Set.piecewise, ht]
  have htI : Integrable (fun ω => bitR (M.T ω)) μ := by
    simpa only [mul_one] using
      integrable_treatment_mul μ M hT (fun _ => 1) (integrable_const (1 : ℝ))
  have hxArm : ∀ t j, eventMean μ (completedArm M t) (fun ω => M.X ω j) =
      ∫ ω, M.X ω j ∂μ := by
    intro t j
    have hh := congrArg (fun ν : Measure (Fin k → ℝ) => ν.map (fun x => x j)) (hArm t).2
    rw [Measure.map_map (measurable_pi_apply j) hX,
      Measure.map_map (measurable_pi_apply j) hX] at hh
    exact event_mean_of_preserved_law μ _ _ ((measurable_pi_apply j).comp hX) hh
  have htArm : ∀ t, eventMean μ (completedArm M t) (fun ω => bitR (M.T ω)) = bitR t := by
    intro t
    have h := arm_mean_treatment_mul μ M hT hR t (fun _ => 1)
    simpa only [mul_one, event_mean_const μ _ (hq t) 1] using h
  have hTMean : eventMean μ (completedEvent M) (fun ω => bitR (M.T ω)) =
      respondentTreatmentProbability μ M := by
    rw [hMixture.2 _ htI.integrableOn, htArm false, htArm true]
    simp [bitR]
  have hXMean : ∀ j, eventMean μ (completedEvent M) (fun ω => M.X ω j) =
      ∫ ω, M.X ω j ∂μ := by
    intro j
    rw [hMixture.2 _ (hxI j).integrableOn, hxArm false j, hxArm true j]
    ring
  have hTXMean : ∀ j, eventMean μ (completedEvent M) (fun ω => bitR (M.T ω)*M.X ω j) =
      respondentTreatmentProbability μ M * ∫ ω, M.X ω j ∂μ := by
    intro j
    rw [hMixture.2 _ (integrable_treatment_mul μ M hT _ (hxI j)).integrableOn,
      arm_mean_treatment_mul μ M hT hR false, arm_mean_treatment_mul μ M hT hR true,
      hxArm false j, hxArm true j]
    simp [bitR]
  refine ⟨hMixture.1, event_mean_const μ _ hE 1, hTMean, ?_, hXMean, hTXMean, ?_, ?_, ?_, ?_⟩
  · have he : (fun ω => bitR (M.T ω)^2) = (fun ω => bitR (M.T ω)) := by
      funext ω; cases ht : M.T ω <;> norm_num [bitR, ht]
    rw [he]; exact hTMean
  · rw [hMixture.2 _ hyRealI.integrableOn, (hArm false).1, (hArm true).1]
  · rw [hMixture.2 _ (integrable_treatment_mul μ M hT _ hyRealI).integrableOn,
      arm_mean_treatment_mul μ M hT hR false, arm_mean_treatment_mul μ M hT hR true,
      (hArm false).1, (hArm true).1]
    simp [bitR]
  · intro j
    have he : (fun ω => (bitR (M.T ω)-respondentTreatmentProbability μ M)*M.X ω j) =
        (fun ω => bitR (M.T ω)*M.X ω j - respondentTreatmentProbability μ M*M.X ω j) := by
      funext ω; ring
    rw [he, event_mean_sub μ _ _ _
      (integrable_treatment_mul μ M hT _ (hxI j)).integrableOn
      ((hxI j).const_mul _).integrableOn,
      event_mean_const_mul, hTXMean j, hXMean j]
    ring
  · exact integral_sub (hyI true) (hyI false)

/-- Finite algebra behind correction T2(d): if the first two normal equations
have randomized respondent moments, multiplying the intercept equation by `p`
and subtracting identifies the treatment coefficient. Covariate dimension
is arbitrary, and `G` need not be nonsingular. This supporting lemma does
not assume H1/H2 imply those moments; that implication is part of the
general theorem below. -/
theorem ols_treatment_from_moments {k : ℕ}
    (G : Matrix (RegressionIndex k) (RegressionIndex k) ℝ)
    (h β : RegressionIndex k → ℝ) (m : Fin k → ℝ) (p μ₀ μ₁ : ℝ)
    (hp : 0 < p) (hp1 : p < 1)
    (h00 : G (Sum.inl 0) (Sum.inl 0) = 1)
    (h01 : G (Sum.inl 0) (Sum.inl 1) = p)
    (h10 : G (Sum.inl 1) (Sum.inl 0) = p)
    (h11 : G (Sum.inl 1) (Sum.inl 1) = p)
    (h0X : ∀ j, G (Sum.inl 0) (Sum.inr j) = m j)
    (h1X : ∀ j, G (Sum.inl 1) (Sum.inr j) = p * m j)
    (hh0 : h (Sum.inl 0) = (1-p)*μ₀+p*μ₁)
    (hh1 : h (Sum.inl 1) = p*μ₁)
    (hNormal : G.mulVec β = h) : β (Sum.inl 1) = μ₁-μ₀ := by
  have e0 := congrFun hNormal (Sum.inl 0)
  have e1 := congrFun hNormal (Sum.inl 1)
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
    h00, h01, h10, h11, one_mul, hh0, hh1, h0X, h1X] at e0 e1
  have es : (∑ j, p * m j * β (Sum.inr j)) = p * ∑ j, m j * β (Sum.inr j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [es] at e1
  have ep := congrArg (fun z : ℝ => p*z) e0
  have hcoef : p * (1-p) ≠ 0 := ne_of_gt (mul_pos hp (sub_pos.mpr hp1))
  have ez : p * (1-p) * (β (Sum.inl 1) - (μ₁-μ₀)) = 0 := by
    nlinarith [e1, ep]
  have := (mul_eq_zero.mp ez).resolve_left hcoef
  linarith

/-- The concrete failure of the equal-completion-rate implication, correction T2(e).
World A has randomized treatment and equal completion rates, but R(0) is
independent of neither Y(0) alone nor the full (Y(0),Y(1),X) bundle; its
normal-equation solution has nonzero treatment coefficient despite τ=0.
All variables are from the construction in T1. -/
def EqualCompletionFailure : Prop :=
  finiteIndependent worldAWeight worldAModel.T worldABundle ∧
  (∀ t : Bool, finiteCondProb worldAWeight
    (fun ω => realizedCompletion worldAModel ω = true) (fun ω => worldAModel.T ω = t) = 1/2) ∧
  ¬ finiteIndependent worldAWeight (worldAModel.R false) (fun ω => ω 0) ∧
  ¬ finiteIndependent worldAWeight (worldAModel.R false) (fun ω => (ω 0, ω 0, ω 3)) ∧
  worldAEffect = 0 ∧ worldAGram.mulVec witnessBeta = worldARhs ∧
  witnessBeta 1 = 12/25 ∧ witnessBeta 1 ≠ worldAEffect

/-- Correction T2(e), reusing T1's exact witness: H1 and equal completion
rates do not imply H2 or identification by complete-case OLS. -/
theorem equal_completion_does_not_identify : EqualCompletionFailure := by
  unfold EqualCompletionFailure finiteIndependent
  decide +kernel

/-- P034-T2(a)-(e), the complete general correction to
amended Study 2 PAP §8 (PDF pp. 5-6), also correcting Appendix pp. 9 and 18.
H1 is randomized treatment with overlap; H2 is independent potential
completion with positive probability. `MemLp ... 2` is the stated finite
second-moment hypothesis; measurability makes these genuine random variables.
No equality of completion rates is an identifying hypothesis. The second
conjunct records the explicit failure of that implication, part (e). -/
theorem corrected_complete_case_identification
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : SurveyModel Ω ℝ k)
    (hT : Measurable M.T) (hY : ∀ t, Measurable (M.Y t))
    (hR : ∀ t, Measurable (M.R t)) (hX : Measurable M.X)
    (hY2 : ∀ t, MemLp (M.Y t) 2 μ) (hX2 : MemLp M.X 2 μ)
    (hH1 : IndepFun M.T (potentialBundle M) μ)
    (hOverlap : 0 < μ.real {ω | M.T ω = true} ∧ μ.real {ω | M.T ω = true} < 1)
    (hH2 : ∀ t : Bool, IndepFun (M.R t) (outcomeCovariateBundle M) μ ∧
      0 < μ.real {ω | M.R t ω = true}) : CompleteCaseIdentification μ M ∧ EqualCompletionFailure := by
  refine ⟨?_, equal_completion_does_not_identify⟩
  have hSel := potential_selected_laws μ M hT hY hR hX hH1 hOverlap hH2
  have hArm := corrected_arm_means_and_covariates μ M hT hY hR hX hH1 hOverlap hH2
  have hm := corrected_respondent_moments μ M hT hY hR hX hY2 hX2 hH1 hOverlap hH2
  unfold CompleteCaseIdentification
  refine ⟨(fun t => ⟨(hSel t).1, (hSel t).2.1⟩), hm.overlap,
    (fun t => (hArm t).1), ?_, (fun t => (hArm t).2), hm.covarianceZero, ?_, ?_⟩
  · rw [(hArm true).1, (hArm false).1, hm.effectContrast]
  · intro β hNormal
    have hg00 : populationGram μ M (Sum.inl 0) (Sum.inl 0) = 1 := by
      simpa [populationGram, populationDesign] using hm.oneMean
    have hg01 : populationGram μ M (Sum.inl 0) (Sum.inl 1) =
        respondentTreatmentProbability μ M := by
      simpa [populationGram, populationDesign] using hm.treatmentMean
    have hg10 : populationGram μ M (Sum.inl 1) (Sum.inl 0) =
        respondentTreatmentProbability μ M := by
      simpa [populationGram, populationDesign] using hm.treatmentMean
    have hg11 : populationGram μ M (Sum.inl 1) (Sum.inl 1) =
        respondentTreatmentProbability μ M := by
      simpa [populationGram, populationDesign, pow_two] using hm.treatmentSquareMean
    have hg0X : ∀ j, populationGram μ M (Sum.inl 0) (Sum.inr j) = ∫ ω, M.X ω j ∂μ := by
      intro j
      simpa [populationGram, populationDesign] using hm.covariateMean j
    have hg1X : ∀ j, populationGram μ M (Sum.inl 1) (Sum.inr j) =
        respondentTreatmentProbability μ M * ∫ ω, M.X ω j ∂μ := by
      intro j
      simpa [populationGram, populationDesign] using hm.treatmentCovariateMean j
    have hh0 : populationRhs μ M (Sum.inl 0) =
        (1-respondentTreatmentProbability μ M)*(∫ ω, M.Y false ω ∂μ) +
        respondentTreatmentProbability μ M*(∫ ω, M.Y true ω ∂μ) := by
      simpa [populationRhs, populationDesign] using hm.outcomeMean
    have hh1 : populationRhs μ M (Sum.inl 1) =
        respondentTreatmentProbability μ M*(∫ ω, M.Y true ω ∂μ) := by
      simpa [populationRhs, populationDesign] using hm.treatmentOutcomeMean
    have hb := ols_treatment_from_moments (populationGram μ M) (populationRhs μ M) β
      (fun j => ∫ ω, M.X ω j ∂μ) (respondentTreatmentProbability μ M)
      (∫ ω, M.Y false ω ∂μ) (∫ ω, M.Y true ω ∂μ) hm.overlap.1 hm.overlap.2
      hg00 hg01 hg10 hg11 hg0X hg1X hh0 hh1 hNormal
    exact hb.trans hm.effectContrast.symm
  · intro hdet
    have hu : IsUnit (populationGram μ M) :=
      (populationGram μ M).isUnit_iff_isUnit_det.mpr hdet
    obtain ⟨β, hβ⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hu) (populationRhs μ M)
    refine ⟨β, hβ, ?_⟩
    intro β' hβ'
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hu) (hβ'.trans hβ.symm)


end AronowAudit.P034

