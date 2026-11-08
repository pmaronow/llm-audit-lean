import Mathlib
import SAP.P042.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042

noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory
open Classical

/-- The actual standard Gaussian distribution function. -/
def standardNormalCDF (x : ℝ) : ℝ := (gaussianReal 0 1).real (Set.Iic x)

/-- The unrounded standard Gaussian 0.975 quantile. Its defining set is certified
nonempty and bounded below in `Normal975Certificate`. -/
def normal975 : ℝ := sInf {x : ℝ | (39 : ℝ) / 40 ≤ standardNormalCDF x}

/-- Existence, inverse-CDF interpretation, and the multiplier enclosure used below. -/
def Normal975Certificate : Prop :=
  {x : ℝ | (39 : ℝ) / 40 ≤ standardNormalCDF x}.Nonempty ∧
  BddBelow {x : ℝ | (39 : ℝ) / 40 ≤ standardNormalCDF x} ∧
  standardNormalCDF normal975 = 39 / 40 ∧
  (19599 : ℝ) / 10000 ≤ normal975 ∧ normal975 ≤ 49 / 25

/-- The two integer coverage events and their exact product-binomial probabilities
at a specified multiplier. Probabilities are represented by the normalized rational
finite expectation already used by `BinomialWitness`. -/
def BinomialMultiplierFacts (z : ℝ) : Prop :=
  (∀ x0 x1 x2 : Fin 101,
    let q : ℤ := (x1.val : ℤ) + (x2.val : ℤ) - 2 * (x0.val : ℤ)
    (coversZero (binomialPooled x0 x1 x2 : ℝ)
      (z * Real.sqrt (1 / 400)) ↔ |q| ≤ 19) ∧
    (coversZero (binomialPooled x0 x1 x2 : ℝ)
      (z * Real.sqrt (3 / 800)) ↔ |q| ≤ 24)) ∧
  binomialTripleExpectation (fun x0 x1 x2 =>
    if coversZero (binomialPooled x0 x1 x2 : ℝ)
      (z * Real.sqrt (1 / 400)) then 1 else 0) = binomialCoverage 19 ∧
  binomialTripleExpectation (fun x0 x1 x2 =>
    if coversZero (binomialPooled x0 x1 x2 : ℝ)
      (z * Real.sqrt (3 / 800)) then 1 else 0) = binomialCoverage 24

/-- P042-T1; pooling on p. 31 (PDF p. 7), intervals on pp. 31–33, shared control on p. 36.
The two constructed sharp-null shared-control witnesses have true pooled variance
three halves of the precision calculation's diagonal variance. The six-voter witness
has the stated 90 allocations and exact moments. The independent binomial-arm witness
has all stated moments, weights, exact coverage sums, reduced fraction, and strict
coverage bounds. Its coverage thresholds are 19 and 24 both for 1.96 and for the actual
standard normal 0.975 quantile, indeed for every multiplier in [1.9599, 1.96].
The usual measure-theoretic conditions are assumed; these finite laws satisfy them.
These are constructed witnesses, with no assertion about historical interval coverage. -/
def T1WholeStatement : Prop :=
  T1Statement ∧ Normal975Certificate ∧
  (∀ z : ℝ, 19599 / 10000 ≤ z → z ≤ 49 / 25 → BinomialMultiplierFacts z) ∧
  BinomialMultiplierFacts normal975

/-- All strict, reversed, and non-strict square-root-free endpoint comparisons.
Nonnegative multiplier and variance and the two positive gaps are essential. -/
def EndpointSquareLaw : Prop :=
  ∀ μ L U z V : ℝ, L < μ → μ < U → 0 ≤ z → 0 ≤ V →
    (L < μ - z * Real.sqrt V ↔ z ^ 2 * V < (μ - L) ^ 2) ∧
    (L ≤ μ - z * Real.sqrt V ↔ z ^ 2 * V ≤ (μ - L) ^ 2) ∧
    (μ - z * Real.sqrt V < L ↔ (μ - L) ^ 2 < z ^ 2 * V) ∧
    (μ - z * Real.sqrt V ≤ L ↔ (μ - L) ^ 2 ≤ z ^ 2 * V) ∧
    (μ + z * Real.sqrt V < U ↔ z ^ 2 * V < (U - μ) ^ 2) ∧
    (μ + z * Real.sqrt V ≤ U ↔ z ^ 2 * V ≤ (U - μ) ^ 2) ∧
    (U < μ + z * Real.sqrt V ↔ (U - μ) ^ 2 < z ^ 2 * V) ∧
    (U ≤ μ + z * Real.sqrt V ↔ (U - μ) ^ 2 ≤ z ^ 2 * V)

/-- Endpoint and squared-radius monotonicity, including the endpoint-check principle
on every nonnegative multiplier interval. Closed bounds also transport strict bins
by transitivity with the appropriate endpoint's strict bound. -/
def EndpointMonotonicityLaw : Prop :=
  ∀ μ V : ℝ, 0 ≤ V →
    Antitone (fun z : ℝ => μ - z * Real.sqrt V) ∧
    Monotone (fun z : ℝ => μ + z * Real.sqrt V) ∧
    MonotoneOn (fun z : ℝ => z ^ 2 * V) (Set.Ici 0) ∧
    (∀ a b z : ℝ, 0 ≤ a → a ≤ z → z ≤ b →
      μ - b * Real.sqrt V ≤ μ - z * Real.sqrt V ∧
      μ - z * Real.sqrt V ≤ μ - a * Real.sqrt V ∧
      μ + a * Real.sqrt V ≤ μ + z * Real.sqrt V ∧
      μ + z * Real.sqrt V ≤ μ + b * Real.sqrt V ∧
      a ^ 2 * V ≤ z ^ 2 * V ∧ z ^ 2 * V ≤ b ^ 2 * V)

/-- P042-T3; Note 5 on p. 40 (PDF p. 16), with the declared pooling method on p. 31.
On the two stipulated deposited recorded-call inputs, all displayed exact fixed-effects
and DerSimonian–Laird calculations hold. The fixed-effects estimate and interval do not
round to Note 5's figures, whereas the DerSimonian–Laird ones do. The endpoint statements
hold throughout [1.9599, 1.96] and at the actual standard normal 0.975 quantile. The stated
square-root-free comparisons and endpoint-check monotonicity hold as well.
The usual measure-theoretic conditions are assumed. The inputs are stipulated exact
rationals; agreement with a calculation makes no assertion about historical intent. -/
def T3WholeStatement : Prop :=
  T3Statement ∧ Normal975Certificate ∧
  roboTauSq = (5819247598 : ℝ) / 10000000000 ∧
  (9625 / 10000 < roboFixedMean - normal975 * Real.sqrt roboFixedVariance ∧
    roboFixedMean + normal975 * Real.sqrt roboFixedVariance < 27685 / 10000) ∧
  (3055 / 10000 ≤ roboRandomMean - normal975 * Real.sqrt roboRandomVariance ∧
    roboRandomMean - normal975 * Real.sqrt roboRandomVariance < 3065 / 10000 ∧
    31345 / 10000 ≤ roboRandomMean + normal975 * Real.sqrt roboRandomVariance ∧
    roboRandomMean + normal975 * Real.sqrt roboRandomVariance < 31355 / 10000) ∧
  EndpointSquareLaw ∧ EndpointMonotonicityLaw

/-- P042-T5 partial result; pooling and mail comparison on p. 31, intervals on pp. 31–33.
The two universal diagonal-variance formulas adopted in the audit's mathematical reading
fail for finite probability laws with square-integrable effects of positive variance.
The usual measure-theoretic conditions are assumed. This is a partial variance-formula
result and supplies no refutation of a particular printed historical assertion.
P042-T5 has no whole replacement in this package; its restricted version is retained. -/
def T5VarianceFormulaRefutation : Prop := T5Statement

/-- Assignment indicator as a Boolean. -/
def assignmentIndicator {N : ℕ} (S : Finset (Fin N)) (i : Fin N) : Bool := decide (i ∈ S)

/-- Expectation with an independent uniform sampled subject and a uniform complete
assignment. All uses below have positive population size and nonempty assignment support. -/
def sampledAssignmentExpectation {N : ℕ} (m : ℕ)
    (f : Finset (Fin N) → Fin N → ℝ) : ℝ :=
  finiteExpectation (completeAssignments N m) (fun S => populationMean (f S))

/-- The entire fixed potential-outcome schedule is independent of assignment randomness. -/
def FixedScheduleIndependence : Prop :=
  ∀ (N : ℕ) (Y : Fin N → Bool → ℝ) (Ω : Type) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → Fin N → Bool),
    IndepFun Z (fun _ : Ω => Y) μ

/-- Event factorization expressing independence of a uniform sampled subject's
assignment from every fixed subject attribute, including the pair of potential outcomes
and compliance type. The finite law makes every event measurable. -/
def SampledSubjectIndependence : Prop :=
  ∀ N m : ℕ, 2 ≤ N → 1 ≤ m → m ≤ N - 1 →
    ∀ (A : Type) (U : Fin N → A) (B : Set A) (b : Bool),
    sampledAssignmentExpectation m (fun S i =>
      if assignmentIndicator S i = b ∧ U i ∈ B then 1 else 0) =
    sampledAssignmentExpectation (N := N) m (fun S i =>
      if assignmentIndicator S i = b then 1 else 0) *
      populationMean (fun i => if U i ∈ B then 1 else 0)

/-- The paper's realized turnout-difference/contact-rate estimator. Its claimed
interpretation below is confined to assignments with positive realized contact rate. -/
def contactCaceEstimator {N : ℕ} (m : ℕ) (S : Finset (Fin N))
    (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) : ℝ :=
  (assignedTreatmentMean m S (contactedOutcome S Y c) -
    assignedControlMean m S (contactedOutcome S Y c)) / assignedContactRate m S c

/-- Expose the sample estimator and its cross-multiplied identity whenever defined. -/
def RealizedContactFormula : Prop :=
  ∀ (N m : ℕ), 2 ≤ N → 1 ≤ m → m ≤ N - 1 →
    ∀ (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) (S : Finset (Fin N)),
    S ∈ completeAssignments N m → 0 < assignedContactRate m S c →
    contactCaceEstimator m S Y c =
      (assignedTreatmentMean m S (contactedOutcome S Y c) -
        assignedControlMean m S (contactedOutcome S Y c)) / assignedContactRate m S c ∧
    contactCaceEstimator m S Y c * assignedContactRate m S c =
      assignedTreatmentMean m S (contactedOutcome S Y c) -
        assignedControlMean m S (contactedOutcome S Y c)

def neverTakerCount {N : ℕ} (c : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i => c i = false)).card

/-- Average contact effect among Never-takers; used only when that group is nonempty. -/
def neverTakerEffect {N : ℕ} (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) : ℝ :=
  (∑ i, if c i = false then Y i true - Y i false else 0) / (neverTakerCount c : ℝ)

/-- Change just one subject's contacted potential outcome by a prescribed amount. -/
def perturbContact {N : ℕ} (Y : Fin N → Bool → ℝ) (k : Fin N) (δ : ℝ)
    (i : Fin N) (t : Bool) : ℝ :=
  if i = k ∧ t = true then Y i t + δ else Y i t

def BinarySchedule {N : ℕ} (Y : Fin N → Bool → ℝ) : Prop :=
  ∀ i t, Y i t = 0 ∨ Y i t = 1

/-- Explicit nonidentification of a Never-taker's effect and of the Never-taker
average: two schedules give identical outcomes under every assignment but different
effects. The binary clause keeps both schedules in the turnout model. -/
def NeverTakerNonidentification : Prop :=
  (∀ (N : ℕ) (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) (k : Fin N) (δ : ℝ),
    c k = false → δ ≠ 0 →
    ∃ Y' : Fin N → Bool → ℝ,
      (∀ S, contactedOutcome S Y' c = contactedOutcome S Y c) ∧
      Y' k true - Y' k false = Y k true - Y k false + δ ∧
      neverTakerEffect Y' c = neverTakerEffect Y c + δ / (neverTakerCount c : ℝ) ∧
      Y' k true - Y' k false ≠ Y k true - Y k false ∧
      neverTakerEffect Y' c ≠ neverTakerEffect Y c) ∧
  (∀ (N : ℕ) (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) (k : Fin N),
    BinarySchedule Y → c k = false →
    ∃ Y' : Fin N → Bool → ℝ,
      BinarySchedule Y' ∧
      (∀ S, contactedOutcome S Y' c = contactedOutcome S Y c) ∧
      Y' k true - Y' k false ≠ Y k true - Y k false ∧
      neverTakerEffect Y' c ≠ neverTakerEffect Y c)

/-- P042-T6 complete-randomization specialization of the formal reading (a)–(b4).
Uniform complete randomization is a substantive design assumption. Under that assumption,
the balance, ITT/CACE, illustration, independence, guarded sample-estimator, and Never-taker
nonidentification statements hold. The usual measure-theoretic conditions are assumed.
This specialization alone does not establish the broader printed assertion under S1. -/
def T6CompleteRandomizationStatement : Prop :=
  T6Statement ∧ FixedScheduleIndependence ∧ SampledSubjectIndependence ∧
  RealizedContactFormula ∧ NeverTakerNonidentification

/-- A known finite assignment law with positive weights 3/4 and 1/4. -/
def biasedTwoProbability : Fin 2 → ℝ := ![3 / 4, 1 / 4]

/-- Subject 0 always has turnout 1 and subject 1 always has turnout 0.
The schedule is binary and constant across treatment statuses and random assignments. -/
def biasedTwoOutcome (i : Fin 2) (_t : Bool) : ℝ := if i = 0 then 1 else 0

/-- A realization a assigns just subject a to treatment and the other to control. -/
def biasedTwoAssignment (a : Fin 2) : Finset (Fin 2) := {a}

/-- Expectation under the normalized finite known-probability assignment law.
Its nonnegative masses sum to one, as asserted in `BiasedTwoBalanceCounterexample`. -/
def biasedTwoExpectation (f : Finset (Fin 2) → ℝ) : ℝ :=
  ∑ a : Fin 2, biasedTwoProbability a * f (biasedTwoAssignment a)

/-- The printed equal-expectation balance assertion, restricted only to finite known
probability laws with fixed nonempty arm sizes. Thus failure of this assertion already
contradicts the general printed S1 scope. Every expectation is a normalized finite sum;
all outcomes, assignments, and statistics are measurable on the finite discrete law. -/
def KnownProbabilityBalanceAssertion : Prop :=
  ∀ (N m K : ℕ), 2 ≤ N → 1 ≤ m → m ≤ N - 1 → 0 < K →
    ∀ p : Fin K → ℝ, (∀ a, 0 ≤ p a) → (∑ a, p a) = 1 →
    ∀ S : Fin K → Finset (Fin N), (∀ a, (S a).card = m) →
    ∀ Y : Fin N → Bool → ℝ, BinarySchedule Y → ∀ t : Bool,
      (∑ a, p a * assignedTreatmentMean m (S a) (fun i => Y i t)) =
        ∑ a, p a * assignedControlMean m (S a) (fun i => Y i t)

/-- Explicit facts refuting balance under random assignment with merely known
probabilities: both arms have size one, all masses are strictly positive and normalized,
the outcomes are binary, and the two expected means are 3/4 and 1/4.
The observed assignment contrast has expectation 1/2 despite zero individual effects. -/
def BiasedTwoBalanceCounterexample : Prop :=
  (∀ a, 0 < biasedTwoProbability a) ∧
  (∑ a, biasedTwoProbability a) = 1 ∧
  BinarySchedule biasedTwoOutcome ∧
  (∀ a, (biasedTwoAssignment a).card = 1 ∧
    (Finset.univ \ biasedTwoAssignment a).card = 1) ∧
  (∀ t : Bool,
    biasedTwoExpectation (fun S => assignedTreatmentMean 1 S
      (fun i => biasedTwoOutcome i t)) = 3 / 4 ∧
    biasedTwoExpectation (fun S => assignedControlMean 1 S
      (fun i => biasedTwoOutcome i t)) = 1 / 4 ∧
    populationMean (fun i => biasedTwoOutcome i t) = 1 / 2 ∧
    biasedTwoExpectation (fun S => assignedTreatmentMean 1 S
      (fun i => biasedTwoOutcome i t)) ≠
      biasedTwoExpectation (fun S => assignedControlMean 1 S
        (fun i => biasedTwoOutcome i t))) ∧
  biasedTwoExpectation (fun S =>
    assignedTreatmentMean 1 S (assignedOutcome S biasedTwoOutcome) -
      assignedControlMean 1 S (assignedOutcome S biasedTwoOutcome)) = 1 / 2 ∧
  populationMean (fun i => biasedTwoOutcome i true - biasedTwoOutcome i false) = 0

/-- P042-T6; randomization on pp. 28 and 30, contact/CACE and illustration on p. 32,
potential outcomes in Note 2 on pp. 39–40 (PDF pp. 15–16).
The printed claim is false: random assignment with known probabilities, as defined in
S1, does not by itself ensure equal expected treatment and control potential-outcome
means. With two subjects whose fixed binary outcomes are 1 and 0, assigning just subject
0 with probability 3/4 and just subject 1 with probability 1/4 gives expected means 3/4
and 1/4. Both arms always contain one subject; all probabilities and quantities exist.
The corresponding universal balance assertion is false. The complete-randomization
formal reading (a)–(b4), with its independence, guarded estimator, and nonidentification
clauses, is retained as the separately named substantive-design specialization.
The usual measure-theoretic conditions are assumed; the counterexample is finite. -/
def T6WholeStatement : Prop :=
  BiasedTwoBalanceCounterexample ∧ (¬ KnownProbabilityBalanceAssertion) ∧
  T6CompleteRandomizationStatement

end
end SAP.P042
