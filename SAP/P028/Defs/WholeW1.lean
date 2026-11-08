import Mathlib
import SAP.P028.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

/-! Whole versions for W1. Ordinary event means below are used only on positive
events; the LATE model deliberately imposes no moments on unused potentials. -/

/-- The Section 2 causal data, without an outcome moment assumption. The three
strata encode precisely binary monotonicity, and Y has no assignment argument. -/
structure WholeCausalData (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  probability : IsProbabilityMeasure μ
  S : Ω → Fin 3
  Y : Bool → Ω → ℝ
  Z : Ω → Bool
  measurableS : Measurable S
  measurableY : ∀ d, Measurable (Y d)
  measurableZ : Measurable Z
  randomAssignment : IndepFun (fun ω => (S ω, Y false ω, Y true ω)) Z μ
  armPositive : ∀ z, 0 < μ.real {ω | Z ω = z}
  nonzeroFirstStage : (∫ ω, realBit (treatment (S ω) true) -
    realBit (treatment (S ω) false) ∂μ) ≠ 0

attribute [instance] WholeCausalData.probability

def wholeComplier {Ω : Type*} [MeasurableSpace Ω] (M : WholeCausalData Ω) : Set Ω :=
  {ω | M.S ω = 2}
def wholeArm {Ω : Type*} [MeasurableSpace Ω] (M : WholeCausalData Ω) (z : Bool) : Set Ω :=
  {ω | M.Z ω = z}
def wholeD {Ω : Type*} [MeasurableSpace Ω] (M : WholeCausalData Ω) (ω : Ω) : Bool :=
  treatment (M.S ω) (M.Z ω)
def wholeY {Ω : Type*} [MeasurableSpace Ω] (M : WholeCausalData Ω) (ω : Ω) : ℝ :=
  M.Y (wholeD M ω) ω
def wholeX {Ω : Type*} [MeasurableSpace Ω] (M : WholeCausalData Ω) (z : Bool) (ω : Ω) : ℝ :=
  M.Y (treatment (M.S ω) z) ω
def wholeP {Ω : Type*} [MeasurableSpace Ω] (M : WholeCausalData Ω) : ℝ :=
  M.μ.real (wholeComplier M)
def wholeE {Ω : Type*} [MeasurableSpace Ω] (M : WholeCausalData Ω) (z : Bool) : ℝ :=
  eventMean M.μ (wholeY M) (wholeArm M z)
def wholeC {Ω : Type*} [MeasurableSpace Ω] (M : WholeCausalData Ω) (d : Bool) : ℝ :=
  eventMean M.μ (M.Y d) (wholeComplier M)
def wholeCACE {Ω : Type*} [MeasurableSpace Ω] (M : WholeCausalData Ω) : ℝ :=
  eventMean M.μ (fun ω => M.Y true ω - M.Y false ω) (wholeComplier M)
def wholeStage {Ω : Type*} [MeasurableSpace Ω] (M : WholeCausalData Ω) : ℝ :=
  eventMean M.μ (fun ω => realBit (wholeD M ω)) (wholeArm M true) -
    eventMean M.μ (fun ω => realBit (wholeD M ω)) (wholeArm M false)
def wholeArmMoments {Ω : Type*} [MeasurableSpace Ω] (M : WholeCausalData Ω) : Prop :=
  ∀ z, IntegrableOn (wholeY M) (wholeArm M z) M.μ

/-- A finite observed sample consists of outcomes, treatments and assignments. -/
abbrev WholeSample (n : ℕ) := (Fin n → ℝ) × (Fin n → Bool) × (Fin n → Bool)
def wholeSampleCount {n : ℕ} (s : WholeSample n) (z : Bool) : ℝ :=
  ∑ i, if s.2.2 i = z then 1 else 0
def wholeSampleMean {n : ℕ} (v : Fin n → ℝ) (Z : Fin n → Bool) (z : Bool) : ℝ :=
  (∑ i, if Z i = z then v i else 0) / (∑ i, if Z i = z then (1 : ℝ) else 0)
def wholeSampleE {n : ℕ} (s : WholeSample n) (z : Bool) : ℝ :=
  wholeSampleMean s.1 s.2.2 z
def wholeSampleP {n : ℕ} (s : WholeSample n) : ℝ :=
  wholeSampleMean (fun i => realBit (s.2.1 i)) s.2.2 true -
    wholeSampleMean (fun i => realBit (s.2.1 i)) s.2.2 false
def wholeSampleWald {n : ℕ} (s : WholeSample n) : ℝ :=
  (wholeSampleE s true - wholeSampleE s false) / wholeSampleP s
def wholeSampleCross {n : ℕ} (Z : Fin n → Bool) (v : Fin n → ℝ) : ℝ :=
  ∑ i, (realBit (Z i) - (∑ j, realBit (Z j)) / n) * (v i - (∑ j, v j) / n)

/-- The sample-analogue clause asserts a measurable estimator and its IV identity;
the paper specifies no sampling law or convergence assertion. Empty sample arms and
a zero sample first stage are excluded when interpreting the ordinary ratios. -/
def wholeEmpiricalClause : Prop :=
  ∀ n : ℕ,
    (∀ z, Measurable (fun s : WholeSample n => wholeSampleE s z)) ∧
    Measurable (wholeSampleP (n := n)) ∧ Measurable (wholeSampleWald (n := n)) ∧
    (∀ s : WholeSample n, 0 < wholeSampleCount s false → 0 < wholeSampleCount s true →
      wholeSampleP s ≠ 0 →
      wholeSampleCross s.2.2 (fun i => realBit (s.2.1 i)) ≠ 0 ∧
      wholeSampleWald s = wholeSampleCross s.2.2 s.1 /
        wholeSampleCross s.2.2 (fun i => realBit (s.2.1 i))) ∧
    (∀ s t : WholeSample n, wholeSampleE s false = wholeSampleE t false →
      wholeSampleE s true = wholeSampleE t true → wholeSampleP s = wholeSampleP t →
      wholeSampleWald s = wholeSampleWald t)

/-- P028-T10; Section 2 LATE display, p. 678, and Section 1, p. 677.
The population and observed treatment first stages equal the positive complier
probability. With the usual measure-theoretic conditions (in particular finite
observed arm means), the complier moments exist, the reduced form and both LATE
ratios hold, and measurable sample analogues give the Wald IV statistic. Two bounded
randomized models share the three reported figures and CACE but have different
complier levels. No moments on unused potential outcomes are assumed. -/
def T10WholeStatement : Prop :=
  (∀ (Ω : Type) [MeasurableSpace Ω], ∀ M : WholeCausalData Ω,
    (∫ ω, realBit (treatment (M.S ω) true) - realBit (treatment (M.S ω) false) ∂M.μ) = wholeP M ∧
    wholeStage M = wholeP M ∧ 0 < wholeP M ∧ wholeP M ≤ 1 ∧
    (wholeArmMoments M →
      (∀ d, IntegrableOn (M.Y d) (wholeComplier M) M.μ) ∧
      IntegrableOn (fun ω => M.Y true ω - M.Y false ω) (wholeComplier M) M.μ ∧
      wholeCACE M = wholeC M true - wholeC M false ∧
      wholeE M true - wholeE M false = wholeP M * wholeCACE M ∧
      wholeCACE M = (wholeE M true - wholeE M false) / wholeP M ∧
      wholeCACE M = (wholeE M true - wholeE M false) / wholeStage M)) ∧
  wholeEmpiricalClause ∧ nonidentificationOfLevels

/-! The exact completion and conditional Bernoulli description of the two T1 laws. -/
def wholeCompletion (upper z d : Bool) : ℤ :=
  if upper then (if z then (if d then 8 else 0) else (if d then 0 else 36))
  else (if z then (if d then 0 else 26) else (if d then 1 else 0))
def wholeCompletedCount (upper z d v : Bool) : ℚ :=
  recordedCount z d v + if v then (wholeCompletion upper z d : ℚ)
    else missingCount z d - (wholeCompletion upper z d : ℚ)
def wholeA (u : Bool) : ℚ := wholeCompletedCount u false true true / 80
def wholeB (u : Bool) : ℚ := wholeCompletedCount u true false true / 320
def wholeMu (u d : Bool) : ℚ :=
  if d then (wholeCompletedCount u true true true / 505 - wholeCompletedCount u false true true / 495) / (2047/9999)
  else (wholeCompletedCount u false false true / 495 - wholeCompletedCount u true false true / 505) / (2047/9999)
def wholeQ (u z d v : Bool) : ℚ := recordedCount z d v / wholeCompletedCount u z d v
def wholeBern (p : ℚ) (b : Bool) : ℚ := if b then p else 1-p

/-- The joint mass of the stated three-stage construction. Its product of response
factors encodes conditional independence, including parameters equal to zero or one. -/
def wholeConstructedMass (u : Bool) (a : BinaryAtom) : ℚ :=
  (if a.d0 then
    (if a.d1 then (16/99) * (if a.y0 then 0 else wholeBern (wholeA u) a.y1) else 0)
   else if a.d1 then (2047/9999) * wholeBern (wholeMu u false) a.y0 * wholeBern (wholeMu u true) a.y1
   else (64/101) * (if a.y1 then 0 else wholeBern (wholeB u) a.y0)) *
  wholeBern (wholeQ u false (fd a false) (fy a false)) a.r0 *
  wholeBern (wholeQ u true (fd a true) (fy a true)) a.r1

def wholeCompletionFacts : Prop :=
  (∀ u z d, 0 ≤ wholeCompletion u z d ∧ (wholeCompletion u z d : ℚ) ≤ missingCount z d) ∧
  (∀ u z d v, 0 < wholeCompletedCount u z d v ∧ 0 ≤ wholeQ u z d v ∧ wholeQ u z d v ≤ 1) ∧
  (∀ u, (0 ≤ wholeA u ∧ wholeA u ≤ 1) ∧ (0 ≤ wholeB u ∧ wholeB u ≤ 1) ∧
    ∀ d, 0 ≤ wholeMu u d ∧ wholeMu u d ≤ 1) ∧
  (wholeA false, wholeB false, wholeMu false false, wholeMu false true) =
    (41/80, 39/80, 1423/10235, 6749/10235) ∧
  (wholeA true, wholeB true, wholeMu true false, wholeMu true true) =
    (1/2, 13/32, 7633/10235, 7642/10235)

def wholeSourceTotals : Prop :=
  recordedCount false false true + recordedCount false false false + missingCount false false = 415 ∧
  recordedCount false true true + recordedCount false true false + missingCount false true = 80 ∧
  recordedCount true false true + recordedCount true false false + missingCount true false = 320 ∧
  recordedCount true true true + recordedCount true true false + missingCount true true = 185 ∧
  (415+80 : ℚ) = armCount false ∧ (320+185 : ℚ) = armCount true ∧
  armCount false + armCount true = 1000 ∧
  missingCount false false + missingCount false true + missingCount true false + missingCount true true = 71

def wholeMixedRounding : Prop :=
  |(1594452863/3629163146 : ℝ) - 4393/10000| < 1/20000 ∧
  |(896530960/1244058109 : ℝ) - 7207/10000| < 1/20000

/-- P028-T1; Section 4, p. 679, with the Section 2 assumptions, p. 678.
The two explicit seventeen-atom laws have the stated integer completions, positive
completed counts, Bernoulli parameters, conditional product construction, stratum
probabilities, source table, full and respondent moments, and different complier
means. They satisfy random assignment including response potentials and have the same
recorded-data law; neither complier mean is a real-valued function of that law in all
admissible models. The usual measure-theoretic conditions are assumed. -/
def T1WholeStatement : Prop :=
  T1Statement ∧ wholeCompletionFacts ∧ wholeSourceTotals ∧ wholeMixedRounding ∧
  (∀ u, let M := if u then upperLaw else lowerLaw
    (∀ a : BinaryAtom, fprob M (fun i => M.atom i = a) = wholeConstructedMass u a) ∧
    fprob M (fun i => (M.atom i).d0 = true ∧ (M.atom i).d1 = true) = 16/99 ∧
    fprob M (fun i => (M.atom i).d0 = false ∧ (M.atom i).d1 = false) = 64/101) ∧
  (∀ u : Bool, Function.Injective (if u then upperLaw.atom else lowerLaw.atom)) ∧
  (∀ d, ¬ ∃ F : (Bool × Bool × Bool × Bool → ℚ) → ℝ,
    ∀ M : BinaryLaw, finiteValid M → F (observedLaw M) = (fcy M d : ℝ))

/-! Observed laws and source-law sharpness for T2. -/
def wholeObservation {Ω : Type*} [MeasurableSpace Ω] (M : CausalModel Ω) (T : Response Ω)
    (ω : Ω) : Bool × Bool × Bool × ℝ :=
  (M.Z ω, observedD M ω, T.R ω, realBit (T.R ω) * observedY M ω)
def wholeObservedLaw {Ω : Type*} [MeasurableSpace Ω] (M : CausalModel Ω) (T : Response Ω) :
    Measure (Bool × Bool × Bool × ℝ) := Measure.map (wholeObservation M T) M.μ

def wholeFiniteMeasure (B : BinaryLaw) : Measure (Fin 17 × Bool) :=
  ∑ i : Fin 17, ∑ z : Bool, ENNReal.ofReal (jointMass B i z : ℝ) • Measure.dirac (i,z)
def wholeFiniteObservation (B : BinaryLaw) (ω : Fin 17 × Bool) : Bool × Bool × Bool × ℝ :=
  (ω.2, fd (B.atom ω.1) ω.2, fr (B.atom ω.1) ω.2,
    ((bit (fr (B.atom ω.1) ω.2) * bit (fy (B.atom ω.1) ω.2) : ℚ) : ℝ))
def wholeFiniteObservedLaw (B : BinaryLaw) : Measure (Bool × Bool × Bool × ℝ) :=
  ∑ o : Bool × Bool × Bool × Bool, ENNReal.ofReal (observedLaw B o : ℝ) •
    Measure.dirac (o.1, o.2.1, o.2.2.1, (bit o.2.2.2 : ℝ))

/-- Pointwise realization of a finite latent table, with the assignment appended
independently. Proof evidence is not part of the realization relation. -/
def wholeRealizes (B : BinaryLaw) (M : CausalModel (Fin 17 × Bool)) (T : Response (Fin 17 × Bool)) : Prop :=
  M.μ = wholeFiniteMeasure B ∧
  M.S = (fun ω => if (B.atom ω.1).d0 then 0 else if (B.atom ω.1).d1 then 2 else 1) ∧
  M.Y = (fun d ω => (bit (if d then (B.atom ω.1).y1 else (B.atom ω.1).y0) : ℝ)) ∧
  M.Z = Prod.snd ∧ T.R = (fun ω => fr (B.atom ω.1) ω.2)

def wholeSensitivityLower {Ω : Type*} [MeasurableSpace Ω] (M : CausalModel Ω) (T : Response Ω) (d : Bool) : ℝ :=
  if d then (recordedOutcomeMoment M T true true - recordedOutcomeMoment M T true false - missingOutcomeProbability M T true false) / complierProbability M
  else (recordedOutcomeMoment M T false false - recordedOutcomeMoment M T false true - missingOutcomeProbability M T false true) / complierProbability M
def wholeSensitivityUpper {Ω : Type*} [MeasurableSpace Ω] (M : CausalModel Ω) (T : Response Ω) (d : Bool) : ℝ :=
  if d then (recordedOutcomeMoment M T true true + missingOutcomeProbability M T true true - recordedOutcomeMoment M T true false) / complierProbability M
  else (recordedOutcomeMoment M T false false + missingOutcomeProbability M T false false - recordedOutcomeMoment M T false true) / complierProbability M
def wholeSourceLower (d : Bool) : ℝ := if d then 6749/10235 else 1423/10235
def wholeSourceUpper (d : Bool) : ℝ := if d then 7642/10235 else 7633/10235
def wholeCellIgnorable {Ω : Type*} [MeasurableSpace Ω] (M : CausalModel Ω) (T : Response Ω) : Prop :=
  ∀ d z, 0 < cellProbability M d z →
    0 < M.μ.real (cellEvent M d z ∩ responseEvent T) ∧ responseCellMean M T d z = cellMean M d z

def wholeCellCounterexample : Prop :=
  ∃ (M : CausalModel (Fin 3 × Bool × Bool)) (T : Response (Fin 3 × Bool × Bool)),
    boundedOutcomes M ∧ wholeCellIgnorable M T ∧ mixedResponsePositive M T ∧
    cellProbability M true false = 1/3 ∧ cellProbability M false true = 1/3 ∧
    complierProbability M = 1/3 ∧
    armMean M false = 1/3 ∧ armMean M true = 2/3 ∧
    responseArmMean M T false = 1/2 ∧ responseArmMean M T true = 4/5 ∧
    complierMean M false = 0 ∧ complierMean M true = 1 ∧
    (∀ z, responseArmMean M T z ≠ armMean M z) ∧ ¬ mixedIdentification M T

def wholeSourceAttainment : Prop :=
  ∃ (L U : CausalModel (Fin 17 × Bool)) (TL TU : Response (Fin 17 × Bool)),
    boundedOutcomes L ∧ boundedOutcomes U ∧
    wholeObservedLaw L TL = wholeFiniteObservedLaw lowerLaw ∧
    wholeObservedLaw U TU = wholeFiniteObservedLaw lowerLaw ∧
    (∀ d, complierMean L d = wholeSourceLower d ∧ complierMean U d = wholeSourceUpper d)

def wholeSourceSharpness : Prop :=
  wholeSourceAttainment ∧
  (∀ (Ω : Type) [MeasurableSpace Ω] (M : CausalModel Ω) (T : Response Ω), boundedOutcomes M →
    wholeObservedLaw M T = wholeFiniteObservedLaw lowerLaw →
    ∀ d, wholeSensitivityLower M T d = wholeSourceLower d ∧ wholeSensitivityUpper M T d = wholeSourceUpper d) ∧
  (∀ (d : Bool) (l u : ℝ),
    (∀ (Ω : Type) [MeasurableSpace Ω] (M : CausalModel Ω) (T : Response Ω), boundedOutcomes M →
      wholeObservedLaw M T = wholeFiniteObservedLaw lowerLaw → l ≤ complierMean M d ∧ complierMean M d ≤ u) →
    l ≤ wholeSourceLower d ∧ wholeSourceUpper d ≤ u)

def wholeSourceRounding : Prop :=
  wholeMixedRounding ∧
  |(16568969/38014837 : ℝ) - 4359/10000| < 1/20000 ∧
  |(295510/414829 : ℝ) - 7124/10000| < 1/20000 ∧
  |wholeSourceLower false - 1390/10000| < 1/20000 ∧
  |wholeSourceUpper false - 7458/10000| < 1/20000 ∧
  |wholeSourceLower true - 6594/10000| < 1/20000 ∧
  |wholeSourceUpper true - 7467/10000| < 1/20000

/-- P028-T2; Section 4, p. 679, repaired using Corollary 1, p. 678.
Joint moments identify complier means without positive treatment cells. The stated
mean equalities justify mixed respondent formulas; conditional response independence
suffices. Cellwise mean ignorability justifies reweighting but need not justify the
mixed formulas. With unrestricted response the stated bounds depend only on the
recorded-data law. All source-table values and approximations hold; both endpoints
of each source interval are attained, so no valid interval can be narrower. The usual
measure-theoretic conditions are assumed. -/
def T2WholeStatement : Prop :=
  (∀ (Ω : Type) [MeasurableSpace Ω], T2Statement Ω ∧
    ∀ M : CausalModel Ω,
      eventMean M.μ (fun ω => realBit (observedD M ω)) (armEvent M true) -
        eventMean M.μ (fun ω => realBit (observedD M ω)) (armEvent M false) = complierProbability M) ∧
  wholeCellCounterexample ∧
  (∀ (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω']
    (M : CausalModel Ω) (T : Response Ω) (M' : CausalModel Ω') (T' : Response Ω'),
    boundedOutcomes M → boundedOutcomes M' → wholeObservedLaw M T = wholeObservedLaw M' T' →
    complierProbability M = complierProbability M' ∧
    (∀ d z, recordedOutcomeMoment M T d z = recordedOutcomeMoment M' T' d z ∧
      missingOutcomeProbability M T d z = missingOutcomeProbability M' T' d z) ∧
    (∀ d, wholeSensitivityLower M T d = wholeSensitivityLower M' T' d ∧
      wholeSensitivityUpper M T d = wholeSensitivityUpper M' T' d)) ∧
  wholeSourceSharpness ∧ wholeSourceRounding

def wholeCoordinate (F : ℝ → ℝ → Prop) (d : Bool) : Set ℝ :=
  {x | ∃ x0 x1, F x0 x1 ∧ (if d then x1 else x0) = x}

def wholeMisprintRealization : Prop :=
  ∃ M : CausalModel (Bool × Bool),
    M.μ = (bernoulliMeasure true false ⟨1/2, by constructor <;> norm_num⟩).prod
      (bernoulliMeasure true false ⟨1/2, by constructor <;> norm_num⟩) ∧
    M.S = (fun ω => if ω.1 then 2 else 1) ∧
    M.Y = (fun _ ω => if ω.1 then 1 else 1/2) ∧ M.Z = Prod.snd ∧
    boundedOutcomes M ∧ complierProbability M = 1/2 ∧ M.μ.real (neverEvent M) = 1/2 ∧
    (∀ z, M.μ.real (armEvent M z) = 1/2) ∧
    armMean M false = 3/4 ∧ armMean M true = 3/4 ∧
    complierMean M false = 1 ∧ complierMean M true = 1

/-- P028-T5; proof of Proposition 1 after Eq. (3), p. 678.
The exact candidate (1/2,3/4,3/4,0,0) satisfies the printed system and fails
the constrained mixture equations: its forced noncomplier mean is 3/2. The two
printed feasible coordinate sets are [0,1], while the corrected mixture sets and
Proposition 1 intervals are [1/2,1]. The input triple has the specified realization
with half compliers of outcome one, half never-takers of outcome one half, and
independent fair assignment. The usual measure-theoretic conditions are assumed. -/
def T5WholeStatement : Prop :=
  misprintFacts ∧
  ((3/4 : ℝ) > 1/2 ∧ (3/2 : ℝ) > 1) ∧
  (∀ x0 x1 : ℝ, printedSystem (1/2) (3/4) (3/4) x0 x1 ↔ x0 = x1 ∧ x1 ∈ Set.Icc 0 1) ∧
  (∀ x0 x1 : ℝ, mixtureSystem (1/2) (3/4) (3/4) x0 x1 ↔ x0 = x1 ∧ x1 ∈ Set.Icc (1/2) 1) ∧
  (∀ d, wholeCoordinate (printedSystem (1/2) (3/4) (3/4)) d = Set.Icc 0 1 ∧
    wholeCoordinate (mixtureSystem (1/2) (3/4) (3/4)) d = Set.Icc (1/2) 1) ∧
  wholeMisprintRealization

/-- P028-T6; Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679.
A bounded causal model has positive complier probability at most one, and full
compliance is allowed. The noncomplier contribution gives the mixture identities,
the partial- and full-compliance branches, cell-compatible observable formulas,
both bounds, and singleton boundary intervals. Positive pure cells give the printed
probability-times-mean expression; empty cells have zero product moment. The usual
measure-theoretic conditions are assumed. -/
def T6WholeStatement : Prop :=
  (∀ (Ω : Type) [MeasurableSpace Ω], T6Statement Ω ∧
    ∀ M : CausalModel Ω, boundedOutcomes M →
      (complierProbability M = 1 → ∀ᵐ ω ∂M.μ, ω ∈ complierEvent M) ∧
      (0 < cellProbability M true false → 0 < cellProbability M false true →
        noncomplierContribution M = cellProbability M true false * cellMean M true false +
          cellProbability M false true * cellMean M false true) ∧
      (∀ d z, cellProbability M d z = 0 → jointOutcomeMoment M d z = 0)) ∧
  (∃ M : CausalModel (Bool × Bool), boundedOutcomes M ∧ complierProbability M = 1 ∧
    complierMean M false = 0 ∧ complierMean M true = 1 ∧
    (∀ z, M.μ.real (armEvent M z) = 1/2))

end
end SAP.P028
