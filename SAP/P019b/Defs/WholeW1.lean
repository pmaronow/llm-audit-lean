import Mathlib
import SAP.P019b.Defs
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P019b
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open Classical
/-- A probability model on an arbitrary underlying measurable space. The two counts come from a fixed finite list; bounds are required only almost surely. Binary variables and all observations are measurable. These are the paper's sampling space and its usual measure-theoretic conditions, not a finite-population premise. -/
structure WholeStudy (Ω : Type) [MeasurableSpace Ω] where
  law : Measure Ω
  probability : IsProbabilityMeasure law
  W : Ω → ℕ
  X : Ω → Bool
  Y : Ω → Bool
  Z : Ω → Bool
  V : Ω → ℕ
  measurable_W : Measurable W
  measurable_X : Measurable X
  measurable_Y : Measurable Y
  measurable_Z : Measurable Z
  measurable_V : Measurable V
  bounded : ∃ J : ℕ, ∀ᵐ ω ∂law, W ω ≤ J ∧ V ω ≤ J + 1
attribute [instance] WholeStudy.probability
variable {Ω : Type} [MeasurableSpace Ω]
def WholeStudy.mean (S : WholeStudy Ω) (f : Ω → ℝ) : ℝ := ∫ ω, f ω ∂S.law
def WholeStudy.prob (S : WholeStudy Ω) (D : Ω → Prop) : ℝ :=
  (S.law {ω | D ω}).toReal
/-- Only positive-probability conditioning events are used in the statements. -/
def WholeStudy.ce (S : WholeStudy Ω) (f : Ω → ℝ) (D : Ω → Prop) : ℝ :=
  S.mean (fun ω => if D ω then f ω else 0) / S.prob D
def WholeStudy.variance (S : WholeStudy Ω) (f : Ω → ℝ) : ℝ :=
  S.mean (fun ω => f ω ^ 2) - (S.mean f) ^ 2
def WholeStudy.cv (S : WholeStudy Ω) (f : Ω → ℝ) (D : Ω → Prop) : ℝ :=
  S.ce (fun ω => f ω ^ 2) D - (S.ce f D) ^ 2
def WholeStudy.monotone (S : WholeStudy Ω) : Prop :=
  ∀ᵐ ω ∂S.law, S.Y ω = true → S.X ω = true
def WholeStudy.noLiarsDesign (S : WholeStudy Ω) : Prop :=
  ∀ᵐ ω ∂S.law, (S.V ω : ℝ) = (S.W ω : ℝ) + bitVal (S.X ω) * bitVal (S.Z ω)
def WholeStudy.treatmentIndependent (S : WholeStudy Ω) : Prop :=
  IndepFun (fun ω => (S.W ω, S.X ω, S.Y ω)) S.Z S.law
def WholeStudy.cell (S : WholeStudy Ω) (z y : Bool) (ω : Ω) : Prop :=
  S.Z ω = z ∧ S.Y ω = y
def WholeStudy.nondegenerate (S : WholeStudy Ω) : Prop :=
  (∀ z y, 0 < S.prob (S.cell z y) ∧
    0 < S.cv (fun ω => (S.V ω : ℝ)) (S.cell z y)) ∧
  0 < S.variance (fun ω => bitVal (S.Z ω)) ∧
  0 < S.variance (fun ω => bitVal (S.Y ω))
def WholeStudy.standing (S : WholeStudy Ω) : Prop :=
  S.monotone ∧ S.noLiarsDesign ∧ S.treatmentIndependent ∧ S.nondegenerate
def WholeStudy.mu (S : WholeStudy Ω) : ℝ := S.prob (fun ω => S.X ω = true)
def WholeStudy.listMean (S : WholeStudy Ω) (z y : Bool) : ℝ :=
  S.ce (fun ω => (S.V ω : ℝ)) (S.cell z y)
def WholeStudy.combined (S : WholeStudy Ω) : ℝ :=
  S.mean (fun ω => bitVal (S.Y ω)) + S.mean (fun ω => 1 - bitVal (S.Y ω)) *
    (S.listMean true false - S.listMean false false)
def WholeStudy.beta (S : WholeStudy Ω) : ℝ :=
  S.listMean true true - S.listMean false true
def WholeStudy.falseMass (S : WholeStudy Ω) : ℝ :=
  S.prob (fun ω => S.X ω = false ∧ S.Y ω = true)
def WholeStudy.confessorX (S : WholeStudy Ω) : ℝ :=
  S.ce (fun ω => bitVal (S.X ω)) (fun ω => S.Y ω = true)
def WholeStudy.controlAtom (S : WholeStudy Ω) (t : ℝ) : ℝ :=
  S.ce (fun ω => if (S.V ω : ℝ) = t then 1 else 0) (S.cell false true)
def WholeStudy.treatedAtom (S : WholeStudy Ω) (t : ℝ) : ℝ :=
  S.ce (fun ω => if (S.V ω : ℝ) = t + 1 then 1 else 0) (S.cell true true)
/-- Equality of the control law and the treated law shifted down by one, conditional on a positive direct answer. Counts have finite support almost surely, so these point probabilities determine the full conditional laws. -/
def WholeStudy.shiftedNull (S : WholeStudy Ω) : Prop :=
  0 < S.prob (S.cell false true) ∧ 0 < S.prob (S.cell true true) ∧
    ∀ t : ℝ, S.controlAtom t = S.treatedAtom t
def WholeStudy.cellCount (S : WholeStudy Ω) {n : ℕ} (s : Fin n → Ω)
    (z y : Bool) : ℕ := ∑ i, if S.cell z y (s i) then 1 else 0
def WholeStudy.cellMean (S : WholeStudy Ω) {n : ℕ} (s : Fin n → Ω)
    (z y : Bool) (c : ℝ) : ℝ :=
  if S.cellCount s z y = 0 then c else
    (∑ i, if S.cell z y (s i) then (S.V (s i) : ℝ) else 0) / (S.cellCount s z y : ℝ)
/-- Unbiased within-cell variance; zero in cells with fewer than two subjects. -/
def WholeStudy.cellVariance (S : WholeStudy Ω) {n : ℕ} (s : Fin n → Ω)
    (z y : Bool) : ℝ :=
  if S.cellCount s z y < 2 then 0 else
    (∑ i, if S.cell z y (s i) then
      ((S.V (s i) : ℝ) - S.cellMean s z y 0)^2 else 0) / ((S.cellCount s z y : ℝ) - 1)
def WholeStudy.betaHat (S : WholeStudy Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.cellMean s true true c1 - S.cellMean s false true c0
/-- The printed variance estimate; a fixed real cV completes deficient samples. -/
def WholeStudy.betaVarianceHat (S : WholeStudy Ω) {n : ℕ} (s : Fin n → Ω)
    (cV : ℝ) : ℝ :=
  if 2 ≤ S.cellCount s true true ∧ 2 ≤ S.cellCount s false true then
    S.cellVariance s true true / (S.cellCount s true true : ℝ) +
      S.cellVariance s false true / (S.cellCount s false true : ℝ)
  else cV
/-- Independent draws of subjects; the empty product is the one-point sample law. -/
def WholeStudy.iid (S : WholeStudy Ω) (n : ℕ) : Measure (Fin n → Ω) :=
  Measure.pi (fun _ : Fin n => S.law)
def WholeStudy.sampleProb (S : WholeStudy Ω) (n : ℕ)
    (D : (Fin n → Ω) → Prop) : ℝ := ((S.iid n) {s | D s}).toReal
def WholeStudy.weakLimit (S : WholeStudy Ω)
    (T : (n : ℕ) → (Fin n → Ω) → ℝ) (Q : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun n => ∫ s, f (T n s) ∂S.iid n) atTop (nhds (∫ x, f x ∂Q))
/-- The normal limit and the interior CDF limits of the printed p-value. Every fixed completion is quantified. Lean's division and square root give statistic zero at nonpositive completed variance, and hence p-value one. -/
def WholeStudy.betaInference (S : WholeStudy Ω) : Prop :=
  ∀ c1 c0 cV : ℝ,
    S.weakLimit (fun _ s => (S.betaHat s c1 c0 - 1) /
      Real.sqrt (S.betaVarianceHat s cV)) (gaussianReal 0 1) ∧
    ∀ u : ℝ, 0 < u → u < 1 →
      Tendsto (fun n => S.sampleProb n (fun s =>
        normalPValue (S.betaHat s c1 c0) 1 (S.betaVarianceHat s cV) ≤ u)) atTop (nhds u)
/-- A finite observable encoding, not a finite underlying population. The atom masses specify the entire pushforward law. Coordinate recovery is almost sure. -/
def WholeEncoding (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m))
    (e : Ω → Fin m) : Prop :=
  Measurable e ∧
  (∀ i, S.law {ω | e ω = i} = ENNReal.ofReal (F.law.mass i)) ∧
  ∀ᵐ ω ∂S.law, F.W (e ω) = S.W ω ∧ F.X (e ω) = S.X ω ∧
    F.Y (e ω) = S.Y ω ∧ F.Z (e ω) = S.Z ω ∧ F.V (e ω) = S.V ω
/-- Exact one-subject quantities and almost-sure support assumptions. Independence is transported separately. Negating the monotonicity equivalence preserves almost-sure failure rather than failure at a null point. -/
structure WholePopulationAgreement (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) : Prop where
  monotone_iff : S.monotone ↔ F.monotone
  noLiarsDesign_iff : S.noLiarsDesign ↔ F.noLiarsDesign
  nondegenerate_iff : S.nondegenerate ↔ F.nondegenerate
  cellProb_eq : ∀ z y, S.prob (S.cell z y) = F.law.prob (F.cell z y)
  mu_eq : S.mu = F.mu
  combined_eq : S.combined = F.combined
  beta_eq : S.beta = F.beta
  falseMass_eq : S.falseMass = F.law.prob (fun i => F.X i = false ∧ F.Y i = true)
  confessorProb_eq : S.prob (fun ω => S.Y ω = true) = F.law.prob (fun i => F.Y i = true)
  confessorX_eq : S.confessorX = F.law.ce (fun i => bitVal (F.X i)) (fun i => F.Y i = true)
  controlAtom_eq : ∀ t, S.controlAtom t =
    F.law.ce (fun i => if (F.V i : ℝ) = t then 1 else 0) (F.cell false true)
  treatedAtom_eq : ∀ t, S.treatedAtom t =
    F.law.ce (fun i => if (F.V i : ℝ) = t + 1 then 1 else 0) (F.cell true true)
/-- Transport the entire finite-sample law of the estimate and its variance. Arbitrary real functions are permitted: the encoded sample has finite range, which also supplies integrability. The event clause uses genuine probabilities. -/
def WholeBetaSamplingAgreement (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) : Prop :=
  ∀ (n : ℕ) (c1 c0 cV : ℝ),
    (∀ g : ℝ → ℝ → ℝ,
      Integrable (fun s => g (S.betaHat s c1 c0) (S.betaVarianceHat s cV)) (S.iid n) ∧
      (∫ s, g (S.betaHat s c1 c0) (S.betaVarianceHat s cV) ∂S.iid n) =
        (F.law.iid n).mean (fun s => g (F.betaHat s c1 c0) (F.betaVarianceHat s cV))) ∧
    (∀ D : ℝ → ℝ → Prop,
      NullMeasurableSet {s | D (S.betaHat s c1 c0) (S.betaVarianceHat s cV)} (S.iid n) ∧
      S.sampleProb n (fun s => D (S.betaHat s c1 c0) (S.betaVarianceHat s cV)) =
        (F.law.iid n).prob (fun s => D (F.betaHat s c1 c0) (F.betaVarianceHat s cV)))
/-- P019-T12; Proposition 3, p. 50 (PDF p. 8), and Section 5.3, p. 56 (PDF p. 14): Assumptions 1–3 and defined confessor cells give beta = 1. With Assumption 4, the studentized estimator tends to a standard normal and the printed two-sided p-value is asymptotically uniform, for every fixed completion of undefined sample quantities. Usual measure-theoretic conditions are assumed; the underlying probability space is arbitrary. -/
def T12WholeStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : WholeStudy Ω),
    S.monotone → S.noLiarsDesign → S.treatmentIndependent →
    0 < S.prob (S.cell false true) → 0 < S.prob (S.cell true true) →
    S.beta = 1 ∧ (S.nondegenerate → S.betaInference)
/-- P019-T17; Lemma 1, pp. 47–48 (PDF pp. 5–6): under Assumptions 1–4 the combined functional identifies prevalence. Under Assumptions 2–4 its excess is the false-confession mass, equal to Pr(Y=1)(1-E[X|Y=1]); failure of almost-sure monotonicity is equivalent to positive false-confession mass and to E[X|Y=1] < 1, and gives strict overestimation. Usual measure-theoretic conditions are assumed; the underlying probability space is arbitrary. -/
def T17WholeStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : WholeStudy Ω),
    (S.standing → S.mu = S.combined) ∧
    (S.noLiarsDesign → S.treatmentIndependent → S.nondegenerate →
      0 < S.prob (fun ω => S.Y ω = true) ∧
      S.combined = S.mu + S.falseMass ∧
      S.falseMass = S.prob (fun ω => S.Y ω = true) * (1 - S.confessorX) ∧
      (¬ S.monotone ↔ 0 < S.falseMass) ∧
      (¬ S.monotone ↔ S.confessorX < 1) ∧
      (¬ S.monotone → S.mu < S.combined ∧ S.confessorX < 1))
abbrev WholeObservation := Bool × Bool × ℕ
def WholeStudy.rejectionProb (S : WholeStudy Ω) (n : ℕ)
    (reject : (Fin n → WholeObservation) → Bool) : ℝ :=
  S.sampleProb n (fun s => reject (fun i => (S.Z (s i), S.Y (s i), S.V (s i))) = true)
/-- P019-T21; Section 4.1 and Proposition 3, p. 50 (PDF p. 8): Assumptions 1–3 and defined confessor cells imply equality of the control conditional law and the treated law shifted down by one. Consequently every level-alpha test of that distributional null remains level-alpha under these assumptions. Under Assumptions 1–4, beta = 1, the studentized estimator tends to a standard normal, and the printed two-sided p-value is asymptotically uniform, for every fixed completion. Usual measure-theoretic conditions are assumed; the underlying probability space is arbitrary. -/
def T21WholeStatement : Prop :=
  (∀ (Ω : Type) [MeasurableSpace Ω] (S : WholeStudy Ω),
    S.monotone → S.noLiarsDesign → S.treatmentIndependent →
    0 < S.prob (S.cell false true) → 0 < S.prob (S.cell true true) → S.shiftedNull) ∧
  (∀ (Ω : Type) [MeasurableSpace Ω] (S : WholeStudy Ω),
    S.standing → S.beta = 1 ∧ S.betaInference) ∧
  (∀ (n : ℕ) (α : ℝ) (reject : (Fin n → WholeObservation) → Bool),
    0 ≤ α → α ≤ 1 →
    (∀ (Ω : Type) [MeasurableSpace Ω] (S : WholeStudy Ω),
      S.shiftedNull → S.rejectionProb n reject ≤ α) →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : WholeStudy Ω),
      S.monotone → S.noLiarsDesign → S.treatmentIndependent →
      0 < S.prob (S.cell false true) → 0 < S.prob (S.cell true true) →
      S.rejectionProb n reject ≤ α)
/-- The entire observable probability table, including all zero entries. -/
def wholeCNNAtomMass (z y : Bool) (v : ℕ) : ℝ :=
  if z then
    if y then (if v = 2 ∨ v = 3 then 1/16 else 0)
    else if v = 1 then 1/8 else if v = 2 then 3/16 else if v = 3 then 1/16 else 0
  else if v = 1 ∨ v = 2 then (if y then 1/16 else 3/16) else 0
/-- P019-T13; Table A1, p. 61 (PDF p. 19), and Section 5.2, p. 54 (PDF p. 12): the two CNN worlds have independent type, baseline and assignment, satisfy Assumptions 1–4 for reading-or-watching, and share the complete observable law, with the stated cell and atom tables, moments, contrasts and placebos. Watching prevalence is 1/4 versus 1/2; all answers are truthful in A, whereas the reader-only class becomes withholding watchers in B. Thus no function of the observable law identifies watching throughout these worlds. Usual measure-theoretic conditions are assumed (automatic for this finite witness). -/
def T13WholeStatement : Prop :=
  T13Statement ∧
  (∀ (t : Fin 3) (w : Fin 2) (z : Bool),
    cnnWitness.law.prob (fun ω => ω.val / 4 = t.val ∧
      cnnWitness.W ω = 1 + w.val ∧ cnnWitness.Z ω = z) =
      (if t.val < 2 then 1/4 else 1/2) * (1/2) * (1/2)) ∧
  (∀ t : Fin 3, cnnWitness.law.prob (fun ω => ω.val / 4 = t.val) =
    (if t.val < 2 then 1/4 else 1/2)) ∧
  (∀ w : Fin 2, cnnWitness.law.prob (fun ω => cnnWitness.W ω = 1 + w.val) = 1/2) ∧
  (∀ z : Bool, cnnWitness.law.prob (fun ω => cnnWitness.Z ω = z) = 1/2) ∧
  (∀ (b : Bool) (ω : Fin 12),
    (cnnReading b ω, cnnWatching b ω, cnnWitness.X ω, cnnWitness.Y ω) =
      if ω.val / 4 = 0 then (false, true, true, true)
      else if ω.val / 4 = 1 then (!b, b, true, false)
      else (false, false, false, false)) ∧
  (∀ ω : Fin 12, cnnWitness.W ω = 1 ∨ cnnWitness.W ω = 2) ∧
  (∀ z y : Bool,
    cnnWitness.law.prob (cnnWitness.cell z y) = (if y then 1/8 else 3/8) ∧
    cnnWitness.listMean z y = (if z then (if y then 5/2 else 11/6) else 3/2) ∧
    cnnWitness.law.cv (fun ω => (cnnWitness.V ω : ℝ)) (cnnWitness.cell z y) =
      (if z && !y then 17/36 else 1/4)) ∧
  (cnnWitness.law.variance (fun ω => bitVal (cnnWitness.Y ω)) = 3/16 ∧
    cnnWitness.law.variance (fun ω => bitVal (cnnWitness.Z ω)) = 1/4 ∧
    cnnWitness.law.mean (fun ω => bitVal (cnnWitness.Y ω)) = 1/4 ∧
    cnnWitness.law.mean (fun ω => 1 - bitVal (cnnWitness.Y ω)) = 3/4 ∧
    cnnWitness.law.ce (fun ω => (cnnWitness.V ω : ℝ)) (fun ω => cnnWitness.Z ω = true) -
      cnnWitness.law.ce (fun ω => (cnnWitness.V ω : ℝ)) (fun ω => cnnWitness.Z ω = false) = 1/2) ∧
  (cnnWitness.combined = 1/4 + (3/4) * (11/6 - 3/2)) ∧
  (∀ (z y : Bool) (v : ℕ),
    cnnWitness.law.prob (fun ω => cnnWitness.Z ω = z ∧
      cnnWitness.Y ω = y ∧ cnnWitness.V ω = v) = wholeCNNAtomMass z y v) ∧
  (cnnWitness.Y = cnnWatching false) ∧
  (∀ ω : Fin 12, cnnWitness.X ω = true → cnnWitness.Y ω = false →
    cnnReading false ω = true ∧ cnnWatching false ω = false ∧
    cnnWitness.Y ω = cnnWatching false ω ∧
    cnnReading true ω = false ∧ cnnWatching true ω = true ∧
    cnnWitness.Y ω ≠ cnnWatching true ω) ∧
  (∀ b : Bool,
    cnnWitness.combined = cnnWitness.law.prob (fun ω => cnnWatching b ω = true) ↔ b = true) ∧
  (∀ b : Bool, cnnWitness.combined = cnnWitness.law.prob
    (fun ω => (cnnReading b ω || cnnWatching b ω) = true)) ∧
  (¬ ∃ F : (Bool → Bool → ℕ → ℝ) → ℝ,
    ∀ b : Bool, F wholeCNNAtomMass = cnnWitness.law.prob (fun ω => cnnWatching b ω = true))
abbrev WholeOrderAtom := Bool × Bool × Bool
/-- Latent response R has probability 1/4; baseline B and assignment Z are fair and independent of R and one another. Coordinates are (R,B,Z). -/
def wholeOrderLaw : FiniteLaw WholeOrderAtom where
  mass := fun a => if a.1 then 1/16 else 3/16
  nonneg := by intro a; split <;> norm_num
  total := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]
/-- Disclose assignment, record Y=R xor Z, then present the list. The binary potentials are Y(0)=R and Y(1)=not R; the list count is V=B+Z and X=1. -/
def wholeOrderStudy : Study WholeOrderAtom where
  law := wholeOrderLaw
  W := fun a => if a.2.1 then 1 else 0
  X := fun _ => true
  Y := fun a => xor a.1 a.2.2
  Z := fun a => a.2.2
  V := fun a => (if a.2.1 then 1 else 0) + (if a.2.2 then 1 else 0)
/-- The chronological events of the counterexample protocol. In particular, disclosure of assignment and presentation of the actual list are distinct. -/
inductive WholeOrderEvent where
  | discloseAssignment : Bool → WholeOrderEvent
  | recordDirectAnswer : Bool → WholeOrderEvent
  | presentList : Bool → WholeOrderEvent
  deriving DecidableEq
/-- At time 0 disclose the randomized assignment; at time 1 record the assignment-dependent direct answer; at time 2 present the assigned list. -/
def wholeOrderHistory (a : WholeOrderAtom) (t : Fin 3) : WholeOrderEvent :=
  if t = 0 then .discloseAssignment (wholeOrderStudy.Z a)
  else if t = 1 then .recordDirectAnswer (wholeOrderStudy.Y a)
  else .presentList (wholeOrderStudy.Z a)
/-- P019-T22; Proposition 4, p. 51 (PDF p. 9): Assumption 3 and positive
treatment arms give delta = 0; with Assumption 4, the studentized estimator has
a standard normal limit and the printed two-sided p-value is asymptotically
uniform for every fixed completion. Restricted to finite underlying probability
spaces with arbitrary real atom masses; the extension to arbitrary measurable
spaces, the general randomized causal-effect interpretation, and the positive
delayed-treatment design implication are not formalized. The additional finite
protocol shows failure of independence when assignment is disclosed before the
direct answer and only physical list display is delayed. This does not refute
the printed design assertion. Usual measure-theoretic conditions are automatic
for these finite models. -/
def T22WholeStatement : Prop :=
  T22Statement ∧
  wholeOrderStudy.monotone ∧ wholeOrderStudy.noLiarsDesign ∧ wholeOrderStudy.nondegenerate ∧
  (∀ (f : Bool → Bool → ℝ) (z : Bool),
    wholeOrderLaw.mean (fun a => if wholeOrderStudy.Z a = z then f a.1 a.2.1 else 0) =
      wholeOrderLaw.prob (fun a => wholeOrderStudy.Z a = z) *
        wholeOrderLaw.mean (fun a => f a.1 a.2.1)) ∧
  (∀ z : Bool, wholeOrderLaw.prob (fun a => wholeOrderStudy.Z a = z) = 1/2) ∧
  (∀ a : WholeOrderAtom,
    wholeOrderStudy.Y a = if wholeOrderStudy.Z a then !a.1 else a.1) ∧
  (∀ a : WholeOrderAtom,
    wholeOrderHistory a 0 = .discloseAssignment (wholeOrderStudy.Z a) ∧
    wholeOrderHistory a 1 = .recordDirectAnswer (wholeOrderStudy.Y a) ∧
    wholeOrderHistory a 2 = .presentList (wholeOrderStudy.Z a) ∧
    ∀ t : Fin 3, t < 2 → wholeOrderHistory a t ≠ .presentList (wholeOrderStudy.Z a)) ∧
  (0 : ℕ) < 1 ∧ (1 : ℕ) < 2 ∧
  (∀ z y : Bool,
    wholeOrderLaw.prob (wholeOrderStudy.cell z y) = (if z = y then 3/8 else 1/8) ∧
    wholeOrderLaw.cv (fun a => (wholeOrderStudy.V a : ℝ)) (wholeOrderStudy.cell z y) = 1/4) ∧
  wholeOrderLaw.variance (fun a => bitVal (wholeOrderStudy.Y a)) = 1/4 ∧
  wholeOrderLaw.variance (fun a => bitVal (wholeOrderStudy.Z a)) = 1/4 ∧
  wholeOrderStudy.delta = 1/2 ∧ ¬ wholeOrderStudy.treatmentIndependent
end
end SAP.P019b
