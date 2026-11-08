import Mathlib
import SAP.P045a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a
noncomputable section

/-- The groups receiving the high (`true`) or low (`false`) regime. -/
def w1RegimeSet {G : ℕ} (high : Bool) (H : Finset (Fin G)) : Finset (Fin G) :=
  if high then H else univ \ H

/-- Size of the corresponding regime in a two-regime allocation. -/
def w1RegimeCount (G C : ℕ) (high : Bool) : ℕ := if high then C else G-C

/-- Uniform first stage, followed by any conditional joint distribution of local assignments.
No independence across groups is imposed. -/
def w1JointMass {G : ℕ} {n : Fin G → ℕ} (C : ℕ)
    (Q : Finset (Fin G) → Design (GroupAssignments n))
    (w : Finset (Fin G) × GroupAssignments n) : ℝ :=
  if w.1 ∈ firstStageSets G C then (Q w.1).mass w.2 / (firstStageSets G C).card else 0

/-- Only groups assigned this regime have their coordinate laws specified.
The equality is the finite pushforward definition of a conditional marginal law. -/
def w1CoordinateLaw {G : ℕ} {n : Fin G → ℕ} (C : ℕ) (high : Bool)
    (Q : Finset (Fin G) → Design (GroupAssignments n))
    (q : (g : Fin G) → Assignment (n g) → ℝ) : Prop :=
  ∀ H ∈ firstStageSets G C, ∀ g ∈ w1RegimeSet high H, ∀ z,
    prob (Q H).mass (fun u => u g = z) = q g z

/-- Observed equal-group mean within the specified regime. -/
def w1RegimeMean {G : ℕ} {n : Fin G → ℕ} (C : ℕ) (high : Bool)
    (X : (g : Fin G) → Assignment (n g) → ℝ)
    (w : Finset (Fin G) × GroupAssignments n) : ℝ :=
  (∑ g ∈ w1RegimeSet high w.1, X g (w.2 g)) / w1RegimeCount G C high

/-- The group-averaged arm marginal under an arbitrary local law. -/
def w1ArmTarget {G : ℕ} {n : Fin G → ℕ}
    (q : (g : Fin G) → Assignment (n g) → ℝ)
    (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ) (b : Bool) : ℝ :=
  mean (fun g => mean (fun i => marginal (q g) (y g) i b))

/-- Means, direct contrasts at both regimes, indirect contrast, and total contrast,
all on the same sample space with the same probability law. -/
def w1UnbiasedContrasts {Ω : Type*} [Fintype Ω] (law : Ω → ℝ)
    (X : Bool → Bool → Ω → ℝ) (μ : Bool → Bool → ℝ) : Prop :=
  (∀ high b, expect law (X high b) = μ high b) ∧
  (∀ high, expect law (fun w => X high true w - X high false w) =
    μ high true - μ high false) ∧
  expect law (fun w => X true false w - X false false w) = μ true false - μ false false ∧
  expect law (fun w => X true true w - X false false w) = μ true true - μ false false

/-- Four-unit arm mean conditional on both arms existing. -/
def w1BothArmMean (p : ℝ) (b : Bool) : ℝ :=
  condMean (bernoulli p) (fun z : Assignment 4 => armExists true z ∧ armExists false z)
    (armMean coMembers b)

/-- Individual unconditional marginal and all group/population estimands for the witness. -/
def w1WitnessTargets : Prop :=
  (∀ p : ℝ, 0 < p → p < 1 → ∀ i : Fin 4, expect (bernoulli p) (coMembers i) = 3*p) ∧
  (∀ p : ℝ, 0 < p → p < 1 → ∀ b : Bool,
    mean (fun i : Fin 4 => marginal (bernoulli p) coMembers i b) = 3*p ∧
    mean (fun _g : Fin 2 => mean (fun i : Fin 4 => marginal (bernoulli p) coMembers i b)) = 3*p ∧
    mean (fun i : Fin 4 => expect (bernoulli p) (coMembers i)) = 3*p ∧
    mean (fun _g : Fin 2 => mean (fun i : Fin 4 => expect (bernoulli p) (coMembers i))) = 3*p) ∧
  (∀ b : Bool,
    mean (fun i : Fin 4 => marginal (bernoulli (1/2)) coMembers i b) = 3/2 ∧
    mean (fun i : Fin 4 => marginal (bernoulli (1/4)) coMembers i b) = 3/4) ∧
  (∀ b c : Bool,
    mean (fun i : Fin 4 => marginal (bernoulli (1/2)) coMembers i b) -
      mean (fun i : Fin 4 => marginal (bernoulli (1/4)) coMembers i c) = 3/4) ∧
  mean (fun i : Fin 4 => expect (bernoulli (1/2)) (coMembers i)) -
    mean (fun i : Fin 4 => expect (bernoulli (1/4)) (coMembers i)) = 3/4

/-- P045-T1; p. 310 (PDF p. 22); definitions on pp. 308–309 (PDF pp. 20–21).
The four-unit, two-group co-member schedule refutes Bernoulli arm-ratio unbiasedness.
It has the stated individual, group and population estimands, pointwise arm formulas,
positive conditioning domains and every own-arm and both-arm conditional expectation.
Direct, indirect and total ratios fail as quantified, whereas the overall estimator is unbiased.
The usual measure-theoretic conditions are assumed; here all laws and sums are finite. -/
def T1WholeStatement : Prop :=
  T1Statement ∧ w1WitnessTargets ∧
  (∀ z : Assignment 4,
    (armExists true z ↔ 0 < treatedCount z) ∧
    (armExists false z ↔ treatedCount z < 4) ∧
    (0 < treatedCount z → armMean coMembers true z = (treatedCount z : ℝ)-1) ∧
    (treatedCount z < 4 → armMean coMembers false z = (treatedCount z : ℝ))) ∧
  w1BothArmMean (1/2) true = 1 ∧ w1BothArmMean (1/2) false = 2 ∧
  w1BothArmMean (1/4) true = 13/29 ∧ w1BothArmMean (1/4) false = 42/29 ∧
  (∀ high b : Bool,
    let p : ℝ := if high then 1/2 else 1/4
    prob bernoulliWitnessMass (witnessDomain b high) = prob (bernoulli (n := 4) p) (armExists b) ∧
    0 < prob bernoulliWitnessMass (witnessDomain b high) ∧
    condMean bernoulliWitnessMass (witnessDomain b high) (witnessArm b high) =
      (if high then (if b then 17/15 else 28/15) else (if b then 81/175 else 84/85)) ∧
    condMean bernoulliWitnessMass
      (fun w => witnessDomain true high w ∧ witnessDomain false high w) (witnessArm b high) =
      (if high then (if b then 1 else 2) else (if b then 13/29 else 42/29)))

/-- The original ratios can be biased on positive-denominator events. -/
def w1RatioFailure : Prop :=
  prob (bernoulli (1/2)) (fun z : Assignment 4 => armExists true z) = 15/16 ∧
  condMean (bernoulli (1/2)) (fun z : Assignment 4 => armExists true z)
    (armMean coMembers true) = 17/15 ∧
  mean (fun i : Fin 4 => marginal (bernoulli (1/2)) coMembers i true) = 3/2 ∧
  (17/15 : ℝ) ≠ 3/2 ∧
  (∀ high : Bool,
    condMean bernoulliWitnessMass (fun w => witnessDomain true high w ∧ witnessDomain false high w)
      (witnessDirect high) = -1) ∧
  condMean bernoulliWitnessMass (fun w => witnessDomain false true w ∧ witnessDomain false false w)
    witnessIndirect = 224/255 ∧
  condMean bernoulliWitnessMass (fun w => witnessDomain true true w ∧ witnessDomain false false w)
    witnessTotal = 37/255

/-- A complete joint experiment with Bernoulli group laws at two regimes. -/
def w1BernoulliJointResult : Prop :=
  ∀ (G C : ℕ), 0 < C → C < G → ∀ (n : Fin G → ℕ), (∀ g, 0 < n g) →
    ∀ (p : Bool → ℝ), (∀ high, 0 < p high ∧ p high < 1) →
    ∀ (Q : Finset (Fin G) → Design (GroupAssignments n)),
    (∀ high, w1CoordinateLaw C high Q (fun _ => bernoulli (p high))) →
    ∀ (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ),
    w1UnbiasedContrasts (w1JointMass C Q)
      (fun high b => w1RegimeMean C high (fun g => groupHT (p high) (y g) b))
      (fun high b => w1ArmTarget (fun _ => bernoulli (p high)) y b)

/-- Fixed-count ratios and their marginals under the same joint experiment. -/
def w1CRJointResult : Prop :=
  ∀ (G C : ℕ), 0 < C → C < G → ∀ (n : Fin G → ℕ) (k : Bool → Fin G → ℕ),
    (∀ high g, 0 < k high g ∧ k high g < n g) →
    ∀ (Q : Finset (Fin G) → Design (GroupAssignments n)),
    (∀ high, w1CoordinateLaw C high Q (fun g => crMass (n g) (k high g))) →
    ∀ (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ),
    w1UnbiasedContrasts (w1JointMass C Q)
      (fun high b => w1RegimeMean C high (fun g => armMean (y g) b))
      (fun high b => w1ArmTarget (fun g => crMass (n g) (k high g)) y b) ∧
    (∀ w, 0 < w1JointMass C Q w → ∀ high g, g ∈ w1RegimeSet high w.1 → ∀ b,
      armExists b (w.2 g))

/-- Overall means use arbitrary regime-dependent local laws and no arm conditioning. -/
def w1OverallJointResult : Prop :=
  ∀ (G C : ℕ), 0 < C → C < G → ∀ (n : Fin G → ℕ), (∀ g, 0 < n g) →
    ∀ (q : Bool → (g : Fin G) → Design (Assignment (n g)))
      (Q : Finset (Fin G) → Design (GroupAssignments n)),
    (∀ high, w1CoordinateLaw C high Q (fun g => (q high g).mass)) →
    ∀ (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ),
    expect (w1JointMass C Q) (fun w =>
      w1RegimeMean C true (fun g => groupOverall (y g)) w -
      w1RegimeMean C false (fun g => groupOverall (y g)) w) =
    mean (fun g => mean (fun i => expect (q true g).mass (y g i))) -
      mean (fun g => mean (fun i => expect (q false g).mass (y g i)))

/-- The fixed-count first-stage mean also allows every group to receive the regime. -/
def w1CRSingleResult : Prop :=
  ∀ (G C : ℕ), 0 < C → C ≤ G → ∀ (n k : Fin G → ℕ),
    (∀ g, 0 < k g ∧ k g < n g) →
    ∀ (Q : Finset (Fin G) → Design (GroupAssignments n)),
    w1CoordinateLaw C true Q (fun g => crMass (n g) (k g)) →
    ∀ (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ) b,
    expect (w1JointMass C Q) (w1RegimeMean C true (fun g => armMean (y g) b)) =
      w1ArmTarget (fun g => crMass (n g) (k g)) y b

/-- One-regime overall first-stage averaging, including C=G. -/
def w1OverallSingleResult : Prop :=
  ∀ (G C : ℕ), 0 < C → C ≤ G → ∀ (n : Fin G → ℕ), (∀ g, 0 < n g) →
    ∀ (q : (g : Fin G) → Design (Assignment (n g)))
      (Q : Finset (Fin G) → Design (GroupAssignments n)),
    w1CoordinateLaw C true Q (fun g => (q g).mass) →
    ∀ (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ),
    expect (w1JointMass C Q) (w1RegimeMean C true (fun g => groupOverall (y g))) =
      mean (fun g => mean (fun i => expect (q g).mass (y g i)))

/-- P045-T2; p. 310 (PDF p. 22).
Bernoulli arm ratios can be biased even conditional on a positive denominator.
HT group means, uniform first-stage averages and their direct, indirect and total
contrasts are unbiased for the Bernoulli marginal targets. Fixed-count assignment
instead makes the original ratios unbiased for that design's marginal targets,
which differ under interference. Overall means remain unbiased for arbitrary local
laws. The joint results require only the stated conditional group marginals, allow
cross-group dependence, and include empty Bernoulli arms. All four-unit formulas
and the numerical HT contrast expectations are retained.
The usual measure-theoretic conditions are assumed; all spaces here are finite. -/
def T2WholeStatement : Prop :=
  T2Statement ∧ w1RatioFailure ∧
  (∀ (G C : ℕ), 0 < C → C ≤ G → ∀ (n : Fin G → ℕ), (∀ g, 0 < n g) →
    ∀ p : ℝ, 0 < p → p < 1 →
    ∀ (Q : Finset (Fin G) → Design (GroupAssignments n)),
    w1CoordinateLaw C true Q (fun _ => bernoulli p) →
    ∀ (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ) b,
    expect (w1JointMass C Q) (w1RegimeMean C true (fun g => groupHT p (y g) b)) =
      w1ArmTarget (fun _ => bernoulli p) y b) ∧
  w1BernoulliJointResult ∧ w1CRJointResult ∧ w1OverallJointResult ∧
  w1CRSingleResult ∧ w1OverallSingleResult ∧
  (∀ (n k : ℕ), 0 < k → k < n → ∀ z ∈ fixedAssignments n k, ∀ b : Bool,
    (∑ i, if z i=b then (1 : ℝ) else 0) = (if b then k else n-k : ℕ) ∧
    0 < (∑ i, if z i=b then (1 : ℝ) else 0)) ∧
  (∀ (n : ℕ) (p : ℝ) (y : Fin n → Assignment n → ℝ) (b : Bool) (z : Assignment n),
    ¬armExists b z → groupHT p y b z = 0) ∧
  (∀ k : Fin 4, 0 < k.val → ∀ i : Fin 4, ∀ b : Bool,
    marginal (bernoulli ((k.val : ℝ)/4)) coMembers i b = 3*(k.val : ℝ)/4) ∧
  (∀ high : Bool,
    expect bernoulliWitnessMass (fun w =>
      groupHT (if high then 1/2 else 1/4) coMembers true (if high then witnessHigh w else witnessLow w) -
      groupHT (if high then 1/2 else 1/4) coMembers false (if high then witnessHigh w else witnessLow w)) = 0) ∧
  expect bernoulliWitnessMass (fun w => groupHT (1/2) coMembers false (witnessHigh w) -
    groupHT (1/4) coMembers false (witnessLow w)) = 3/4 ∧
  expect bernoulliWitnessMass (fun w => groupHT (1/2) coMembers true (witnessHigh w) -
    groupHT (1/4) coMembers false (witnessLow w)) = 3/4

abbrev W1ToyOutcome := Finset (Fin 6) × (Fin 6 → Assignment 3)

def w1ToyMass (w : W1ToyOutcome) : ℝ :=
  if w.1 ∈ firstStageSets 6 3 then
    (∏ g, crMass 3 (if g ∈ w.1 then 2 else 1) (w.2 g)) / (firstStageSets 6 3).card else 0

def w1ToySupport : Finset W1ToyOutcome :=
  univ.filter (fun w => w.1 ∈ firstStageSets 6 3 ∧
    ∀ g, w.2 g ∈ fixedAssignments 3 (if g ∈ w.1 then 2 else 1))

def w1ToyPoint (high : Bool) (a b : Fin 3 → ℝ) (w : W1ToyOutcome) : ℝ :=
  selectedMean (n := fun _ : Fin 6 => 3) 3 (fun _ => directGroup a b)
    (w1RegimeSet high w.1, w.2)

def w1ToySampleVar (high : Bool) (a b : Fin 3 → ℝ) (w : W1ToyOutcome) : ℝ :=
  rawSampleVar (w1RegimeSet high w.1) (fun g => directGroup a b (w.2 g))

def w1ToyVest (high : Bool) (a b : Fin 3 → ℝ) (w : W1ToyOutcome) : ℝ :=
  directVarianceEstimate (n := fun _ : Fin 6 => 3) 3 (fun _ => a) (fun _ => b)
    (w1RegimeSet high w.1, w.2)

def w1ToyBaseline (i : Fin 3) : ℝ := (i.val : ℝ)+1

/-- Baseline sum of the unique singleton arm, only used on its fixed-count support. -/
def w1SingletonBaseline (high : Bool) (z : Assignment 3) : ℝ :=
  ∑ i, if z i = !high then w1ToyBaseline i else 0

/-- The variance of the two-unit arm; its domain is always size two on the stated support. -/
def w1TwoArmVariance (high : Bool) (z : Assignment 3) : ℝ :=
  if high then rawSampleVar (treatedSet z) (fun i => w1ToyBaseline i+1)
  else rawSampleVar (univ \ treatedSet z) w1ToyBaseline

/-- P045-T3; p. 310 (PDF p. 22) and p. 311 (PDF p. 23).
In the actual six-group joint toy design, all 14,580 supported outcomes are equally
likely. The additive schedule has direct estimand and estimator mean one, but
variance 1/2 and expected singleton-drop variance estimate 1/3 at either regime.
The singleton and direct-statistic distributions, two-unit sample variance and
expected between-group sample variance give the stated bias -1/6 and ratio 2/3.
The dilated schedules are also downward biased, and the zero-control schedule
gives upward bias. The dropping convention is part of the specified estimator.
The usual measure-theoretic conditions are assumed; all laws here are finite. -/
def T3WholeStatement : Prop :=
  T3Statement ∧
  w1ToySupport.card = 14580 ∧ (∀ w, 0 ≤ w1ToyMass w) ∧ (∑ w, w1ToyMass w) = 1 ∧
  (∀ w, w1ToyMass w = if w ∈ w1ToySupport then 1/14580 else 0) ∧
  (∀ high : Bool,
    let m := if high then 2 else 1
    let x := w1ToyBaseline
    mean (fun i : Fin 3 => (x i+1)-x i) = 1 ∧
    mean (fun _g : Fin 6 => mean (fun i : Fin 3 => (x i+1)-x i)) = 1 ∧
    (∀ z ∈ fixedAssignments 3 m,
      directGroup (fun i => x i+1) x z =
        if high then 4-(3/2)*w1SingletonBaseline high z else (3/2)*w1SingletonBaseline high z-2) ∧
    (∀ t ∈ ({1,2,3} : Finset ℝ), prob (crMass 3 m) (fun z => w1SingletonBaseline high z=t) = 1/3) ∧
    (∀ t ∈ ({-1/2,1,5/2} : Finset ℝ),
      prob (crMass 3 m) (fun z => directGroup (fun i => x i+1) x z=t) = 1/3) ∧
    expect (crMass 3 m) (w1TwoArmVariance high) = 1 ∧
    expect w1ToyMass (w1ToyPoint high (fun i => x i+1) x) = 1 ∧
    variance w1ToyMass (w1ToyPoint high (fun i => x i+1) x) = 1/2 ∧
    expect w1ToyMass (w1ToySampleVar high (fun i => x i+1) x) = 3/2 ∧
    expect w1ToyMass (w1ToyVest high (fun i => x i+1) x) = 1/3 ∧
    expect w1ToyMass (w1ToyVest high (fun i => x i+1) x) -
      variance w1ToyMass (w1ToyPoint high (fun i => x i+1) x) = -1/6 ∧
    expect w1ToyMass (w1ToyVest high (fun i => x i+1) x) /
      variance w1ToyMass (w1ToyPoint high (fun i => x i+1) x) = 2/3) ∧
  variance w1ToyMass (w1ToyPoint true (fun i => 2*w1ToyBaseline i) (fun i => (5/4)*w1ToyBaseline i)) = 9/8 ∧
  expect w1ToyMass (w1ToyVest true (fun i => 2*w1ToyBaseline i) (fun i => (5/4)*w1ToyBaseline i)) = 43/48 ∧
  variance w1ToyMass (w1ToyPoint false (fun i => (3/2)*w1ToyBaseline i) w1ToyBaseline) = 8/9 ∧
  expect w1ToyMass (w1ToyVest false (fun i => (3/2)*w1ToyBaseline i) w1ToyBaseline) = 19/36 ∧
  variance w1ToyMass (w1ToyPoint true w1ToyBaseline (fun _ => 0)) = 1/18 ∧
  expect w1ToyMass (w1ToyVest true w1ToyBaseline (fun _ => 0)) = 1/9 ∧
  (43/48 : ℝ) < 9/8 ∧ (19/36 : ℝ) < 8/9 ∧ (1/18 : ℝ) < 1/9

/-- Assignments in the paper's order (00,01,10,11). -/
def w1TwoAssignment (k : Fin 4) : Assignment 2 :=
  ![![false,false], ![false,true], ![true,false], ![true,true]] k

/-- P045-T5; p. 305 (PDF p. 17); staged package R/make_exposure_map_AS.R, lines 104–121.
The stipulated all-control event is the complement of all-treated, and differs
from the documented all-untreated event. The two-vertex count/event tables,
probabilities and all four HT values for the linear and threshold schedules
exhibit the exact failure and the case where the expectation does not move.
The usual measure-theoretic conditions are assumed; all spaces here are finite. -/
def T5WholeStatement : Prop :=
  T5Statement ∧
  (∀ (n : ℕ) (A : Network n) (z : Assignment n) (i : Fin n),
    (∑ j, bit (z j)*bit (if j=i then true else A.adj j i)) = neighborhoodCount A.adj z i ∧
    (∑ j, bit (if i=j then true else A.adj i j)) = (neighborhood A.adj i).card) ∧
  (∀ i : Fin 2, (neighborhood edge2 i).card = 2 ∧
    ∀ k : Fin 4,
    neighborhoodCount edge2 (w1TwoAssignment k) i = (![0,1,1,2] : Fin 4 → ℕ) k ∧
    (allTreated edge2 (w1TwoAssignment k) i ↔ k=3) ∧
    (badAllControl edge2 (w1TwoAssignment k) i ↔ k≠3) ∧
    (allControl edge2 (w1TwoAssignment k) i ↔ k=0)) ∧
  (∀ k : Fin 4,
    bernoulli (1/2) (w1TwoAssignment k) = 1/4 ∧
    fullHT (bernoulli (1/2)) edge2 linear2 true (w1TwoAssignment k) =
      (![-4,0,0,12] : Fin 4 → ℝ) k ∧
    fullHT (bernoulli (1/2)) edge2 threshold2 false (w1TwoAssignment k) =
      (![-4/3,-4/3,-4/3,12] : Fin 4 → ℝ) k ∧
    fullHT (bernoulli (1/2)) edge2 threshold2 true (w1TwoAssignment k) =
      (![-4,0,0,12] : Fin 4 → ℝ) k) ∧
  (4/3 : ℝ) ≠ 2

/-- Edit only the upper entry of the sole edge before the stipulated copy operation.
The intended branch instead deletes both symmetric entries. -/
def w1RemovalOutput (faulty : Bool) (deleted : Bool) : Fin 4 → Fin 4 → ℝ :=
  fun i j => if faulty then faultyCopy 4
    (fun r s => if r < s ∧ deleted = true then 0 else singleEdge4 r s) i.val j.val
    else if deleted then 0 else singleEdge4 i.val j.val

/-- P045-T7; p. 303 (PDF p. 15), Figure 16.5 p. 304 (PDF p. 16); staged R/functions.R, lines 36 and 55.
Storage-order copying has the stated triangle-order mismatch from dimension four.
The single-edge witness produces exactly the two asserted nonzero entries, is
asymmetric, changes both exposures, and 32 of the 64 binary upper triangles fail
symmetry. At each deletion probability q in [0,1), the complete output law is
(1-q) at the faulty matrix and q at zero; intended deletion instead has (1-q)
at the original matrix and q at zero. No other outputs occur.
The usual measure-theoretic conditions are assumed; these are finite laws. -/
def T7WholeStatement : Prop :=
  T7Statement ∧
  (upperCells 4).map (fun x => (x.2,x.1)) = [(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)] ∧
  Fintype.card (Fin 6 → Bool) = 64 ∧
  (∀ i j : Fin 4, faultyCopy 4 singleEdge4 i.val j.val =
    if (i.val=0 ∧ j.val=3) ∨ (i.val=2 ∧ j.val=1) then 1 else 0) ∧
  (∀ q : ℝ, 0 ≤ q → q < 1 → ∀ faulty : Bool,
    (∀ b : Bool, 0 ≤ (if b then q else 1-q)) ∧
    (∑ b : Bool, (if b then q else 1-q)) = 1 ∧
    (∀ M : Fin 4 → Fin 4 → ℝ,
      prob (fun b : Bool => if b then q else 1-q) (fun b => w1RemovalOutput faulty b = M) =
        (if w1RemovalOutput faulty false = M then 1-q else 0) +
        (if (fun _ _ : Fin 4 => (0 : ℝ)) = M then q else 0)) ∧
    prob (fun b : Bool => if b then q else 1-q)
      (fun b => w1RemovalOutput faulty b = w1RemovalOutput faulty false) = 1-q ∧
    prob (fun b : Bool => if b then q else 1-q)
      (fun b => w1RemovalOutput faulty b = (fun _ _ => 0)) = q ∧
    (∀ M : Fin 4 → Fin 4 → ℝ,
      M ≠ w1RemovalOutput faulty false → M ≠ (fun _ _ => 0) →
      prob (fun b : Bool => if b then q else 1-q) (fun b => w1RemovalOutput faulty b=M) = 0))

end
end SAP.P045a
