import Mathlib

/-!
P029: Beyond LATE (Aronow and Carnegie, 2013).
Definitions, finite counterexamples, and probability identities.
-/

namespace AronowAudit.P029

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Binary variables Z and D, pp. 494-495: "a binary IV ... and a binary
endogenous treatment variable". Bool is converted to its real value 0 or 1. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- Potential outcomes, p. 494: "Y₀ᵢ ... if untreated", "Y₁ᵢ ... if treated",
and "D₀ᵢ ... when assigned to control", "D₁ᵢ ... when assigned to treatment".
Each unit has fixed responses and pretreatment covariates, so exclusion and
SUTVA are represented by the two response functions below. -/
structure PotentialUnit (X : Type*) where
  x : X
  d0 : Bool
  d1 : Bool
  y0 : ℝ
  y1 : ℝ

/-- Individual treatment effect, p. 494: "Y₁ᵢ - Y₀ᵢ". -/
def PotentialUnit.tau {X : Type*} (u : PotentialUnit X) : ℝ := u.y1 - u.y0

/-- Complier, p. 495: "D₀ᵢ = 0 and D₁ᵢ = 1". -/
def PotentialUnit.complier {X : Type*} (u : PotentialUnit X) : Prop :=
  u.d0 = false ∧ u.d1 = true

/-- Defier, p. 495: "D₀ᵢ = 1 and D₁ᵢ = 0". -/
def PotentialUnit.defier {X : Type*} (u : PotentialUnit X) : Prop :=
  u.d0 = true ∧ u.d1 = false

/-- Observed receipt D = D₀ + Z(D₁-D₀), pp. 494-495. -/
def PotentialUnit.receipt {X : Type*} (u : PotentialUnit X) (z : Bool) : Bool :=
  if z then u.d1 else u.d0

/-- Observed outcome Y = Y₀ + D(Y₁-Y₀), exclusion and SUTVA, p. 495. -/
def PotentialUnit.outcome {X : Type*} (u : PotentialUnit X) (z : Bool) : ℝ :=
  if u.receipt z then u.y1 else u.y0

/-- A finite probability law is nonnegative and has total mass one. Finite
counterexamples and finite randomization expectations use these sums;
this does not replace general probability statements. -/
def ValidLaw {L : Type*} [Fintype L] (p : L → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1

/-- Expectation under a finite law, rendering the paper's E, p. 494. -/
def fE {L : Type*} [Fintype L] (p v : L → ℝ) : ℝ := ∑ i, p i * v i

/-- Probability under a finite law, rendering the paper's Pr, p. 495. -/
def fP {L : Type*} [Fintype L] (p : L → ℝ) (A : L → Prop) : ℝ :=
  ∑ i, if A i then p i else 0

/-- Conditional mean on an event, e.g. E(Y₁-Y₀ | D₁>D₀), equation (3), p. 495.
All substantive conditional-mean assertions specify positive conditioning mass. -/
def fCE {L : Type*} [Fintype L] (p v : L → ℝ) (A : L → Prop) : ℝ :=
  fE p (fun i => if A i then v i else 0) / fP p A

/-- Population covariance (denominator N for a uniform finite population),
used in the corrected comparisons. -/
def fCov {L : Type*} [Fintype L] (p u v : L → ℝ) : ℝ :=
  fE p (fun i => u i * v i) - fE p u * fE p v

/-- Population variance, used in the SEM and RMSE corrections. -/
def fVar {L : Type*} [Fintype L] (p v : L → ℝ) : ℝ := fCov p v v

/-- Population correlation when both variances are positive, Section 2.1,
p. 494. Witnesses below explicitly have positive variances. -/
def fCorr {L : Type*} [Fintype L] (p u v : L → ℝ) : ℝ :=
  fCov p u v / Real.sqrt (fVar p u * fVar p v)

/-- Independence on a finite support: joint probabilities factor for every
pair of values. The codomains may be infinite, but the law has finite support. -/
def FIndep {L A B : Type*} [Fintype L] (p : L → ℝ) (U : L → A) (V : L → B) : Prop :=
  ∀ a b, fP p (fun i => U i = a ∧ V i = b) =
    fP p (fun i => U i = a) * fP p (fun i => V i = b)

/-- Independent Bernoulli assignment, p. 495: "Zᵢ is randomly assigned and
thus independent of all potential outcomes". Its probability is e ∈ (0,1). -/
def randomized {L : Type*} (p : L → ℝ) (e : ℝ) : L × Bool → ℝ :=
  fun i => p i.1 * if i.2 then e else 1 - e

/-- The population analogue of the Section 3.3 ratio (p. 498), computed
directly from observed weighted arm means. -/
def fWald {L X : Type*} [Fintype L] (p : L → ℝ) (U : L → PotentialUnit X)
    (Z : L → Bool) (w : L → ℝ) : ℝ :=
  ((fCE p (fun i => w i * (U i).outcome (Z i)) (fun i => Z i = true) /
      fCE p w (fun i => Z i = true)) -
    (fCE p (fun i => w i * (U i).outcome (Z i)) (fun i => Z i = false) /
      fCE p w (fun i => Z i = false))) /
  ((fCE p (fun i => w i * bit ((U i).receipt (Z i))) (fun i => Z i = true) /
      fCE p w (fun i => Z i = true)) -
    (fCE p (fun i => w i * bit ((U i).receipt (Z i))) (fun i => Z i = false) /
      fCE p w (fun i => Z i = false)))

/-- Compliance score, p. 496: "P_Ci = Pr(D₁>D₀ | X=xᵢ)". -/
def fScore {L X : Type*} [Fintype L] (p : L → ℝ) (U : L → PotentialUnit X)
    (x : X) : ℝ := fP p (fun i => (U i).complier ∧ (U i).x = x) /
      fP p (fun i => (U i).x = x)

/-- Assumption 1, p. 499: "E(Y₁-Y₀ | X=x) = E(Y₁-Y₀ | D₁>D₀, X=x)". -/
def fLatentIgnorability {L X : Type*} [Fintype L] (p : L → ℝ)
    (U : L → PotentialUnit X) : Prop :=
  ∀ x, 0 < fP p (fun i => (U i).x = x) →
    fCE p (fun i => (U i).tau) (fun i => (U i).x = x) =
    fCE p (fun i => (U i).tau) (fun i => (U i).complier ∧ (U i).x = x)

/-- The two displayed "typical ignorability" equalities, p. 499. -/
def fTypicalIgnorability {L X : Type*} [Fintype L] (p : L → ℝ)
    (U : L → PotentialUnit X) (Z : L → Bool) (x : X) : Prop :=
  fCE p (fun i => (U i).y0) (fun i => (U i).receipt (Z i) = true ∧ (U i).x = x) =
    fCE p (fun i => (U i).y0) (fun i => (U i).receipt (Z i) = false ∧ (U i).x = x) ∧
  fCE p (fun i => (U i).y1) (fun i => (U i).receipt (Z i) = true ∧ (U i).x = x) =
    fCE p (fun i => (U i).y1) (fun i => (U i).receipt (Z i) = false ∧ (U i).x = x)

/-- Finite rendering of the five IV assumptions, pp. 494-495. Exclusion and
SUTVA are enforced by PotentialUnit's fixed response functions. -/
def FIV {L X : Type*} [Fintype L] (p : L → ℝ) (U : L → PotentialUnit X)
    (Z : L → Bool) : Prop :=
  ValidLaw p ∧ 0 < fP p (fun i => Z i = true) ∧ fP p (fun i => Z i = true) < 1 ∧
  FIndep p (fun i => ((U i).x, (U i).d0, (U i).d1, (U i).y0, (U i).y1)) Z ∧
  fP p (fun i => (U i).defier) = 0 ∧
  fCE p (fun i => bit ((U i).receipt (Z i))) (fun i => Z i = true) -
    fCE p (fun i => bit ((U i).receipt (Z i))) (fun i => Z i = false) ≠ 0

/-- Independent assignment gives a normalized joint law. This is a finite
probability lemma for the paper's random-assignment assumption, p. 495. -/
theorem randomized_valid {L : Type*} [Fintype L] (p : L → ℝ) (e : ℝ)
    (hp : ValidLaw p) (he0 : 0 ≤ e) (he1 : e ≤ 1) : ValidLaw (randomized p e) := by
  constructor
  · intro i
    unfold randomized
    apply mul_nonneg (hp.1 i.1)
    split <;> linarith
  · simp only [randomized, Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    have h : ∀ i, p i * e + p i * (1 - e) = p i := by intro i; ring
    simpa only [h] using hp.2

/-- Randomized assignment is independent of every fixed unit attribute,
including the entire covariate/potential-outcome tuple, p. 495. -/
theorem randomized_independent {L A : Type*} [Fintype L] (p : L → ℝ) (e : ℝ)
    (hp : ValidLaw p) (v : L → A) :
    FIndep (randomized p e) (fun i => v i.1) (fun i => i.2) := by
  classical
  intro a b
  cases b <;>
    simp only [fP, randomized, Fintype.sum_prod_type, Fintype.sum_bool]
  all_goals
    simp only [Bool.true_eq_false, Bool.false_eq_true, and_false, and_true,
      if_false, if_true, Finset.sum_const_zero, add_zero, zero_add]
  all_goals
    have h : ∀ i, (if v i = a then p i * e else 0) +
        (if v i = a then p i * (1 - e) else 0) = if v i = a then p i else 0 := by
      intro i; split_ifs <;> ring
    have hweight (k : ℝ) : ∀ i, (if v i = a then p i*k else 0) =
        (if v i = a then p i else 0)*k := by
      intro i; split_ifs <;> ring
    simp only [h, hweight, ← Finset.sum_mul, hp.2]
    ring

/-- T1/T2/T15 type law: C, A, N have probabilities 1/2, 1/4, 1/4.
The six atoms are (type, assignment); this law is a counterexample construction. -/
def typeMass (i : Fin 3) : ℝ := if i.val = 0 then 1/2 else 1/4

/-- Case 1 (T1): Y₀=0, Y₁=1 for compliers and zero otherwise. -/
def case1Unit (i : Fin 3) : PotentialUnit Unit :=
  ⟨(), decide (i.val = 1), decide (i.val ≠ 2), 0, if i.val = 0 then 1 else 0⟩

/-- Case 2 (T2): Y₀=1 for always-takers and Y₁=Y₀+1. -/
def case2Unit (i : Fin 3) : PotentialUnit Unit :=
  ⟨(), decide (i.val = 1), decide (i.val ≠ 2),
    if i.val = 1 then 1 else 0, (if i.val = 1 then 1 else 0) + 1⟩

/-- The constant-effect law of T13/T15 (P029-E005/P029-E006). -/
def constantUnit (i : Fin 3) : PotentialUnit Unit :=
  ⟨(), decide (i.val = 1), decide (i.val ≠ 2), 0, 1⟩

def sixMass : Fin 3 × Bool → ℝ := randomized typeMass (1/2)
def liftUnit {L X : Type*} (u : L → PotentialUnit X) : L × Bool → PotentialUnit X :=
  fun i => u i.1

/-- T1: the concrete six-atom law satisfies all five IV assumptions and both
displayed ignorability equalities, but its ATE is 1/2 and its complier effect
and true-score ICSW/Wald ratios are 1. It refutes the p. 499 ordering. -/
theorem ignorability_counterexample :
    FIV sixMass (liftUnit case1Unit) Prod.snd ∧
    fTypicalIgnorability sixMass (liftUnit case1Unit) Prod.snd () ∧
    fP sixMass (fun i => (case1Unit i.1).receipt i.2 = true) = 1/2 ∧
    fP sixMass (fun i => (case1Unit i.1).receipt i.2 = false) = 1/2 ∧
    fCE sixMass (fun i => if (case1Unit i.1).complier then 1 else 0)
      (fun i => (case1Unit i.1).receipt i.2 = true) = 1/2 ∧
    fCE sixMass (fun i => if (case1Unit i.1).complier then 1 else 0)
      (fun i => (case1Unit i.1).receipt i.2 = false) = 1/2 ∧
    fE sixMass (fun i => (case1Unit i.1).tau) = 1/2 ∧
    fCE sixMass (fun i => (case1Unit i.1).tau) (fun i => (case1Unit i.1).complier) = 1 ∧
    fScore sixMass (liftUnit case1Unit) () = 1/2 ∧
    (1/4 : ℝ) < fScore sixMass (liftUnit case1Unit) () ∧
    fWald sixMass (liftUnit case1Unit) Prod.snd (fun _ => 1) = 1 ∧
    fWald sixMass (liftUnit case1Unit) Prod.snd
      (fun i => 1 / fScore sixMass (liftUnit case1Unit) (case1Unit i.1).x) = 1 := by
  have ht : ValidLaw typeMass := by
    constructor
    · intro i; unfold typeMass; split <;> norm_num
    · norm_num [typeMass, Fin.sum_univ_succ]
  have hi := randomized_independent typeMass (1/2) ht
    (fun i => ((case1Unit i).x, (case1Unit i).d0, (case1Unit i).d1,
      (case1Unit i).y0, (case1Unit i).y1))
  have hv := randomized_valid typeMass (1/2) ht (by norm_num) (by norm_num)
  refine ⟨⟨hv, ?_, ?_, hi, ?_, ?_⟩, ?_⟩
  all_goals norm_num [fTypicalIgnorability, fCE, fE, fP, fScore, fWald,
    sixMass, liftUnit, randomized, typeMass, case1Unit, bit,
    PotentialUnit.receipt, PotentialUnit.outcome, PotentialUnit.complier,
    PotentialUnit.defier, PotentialUnit.tau, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- T2(b): the same type/assignment law with a constant effect 1 satisfies
Assumption 1, while both displayed received-treatment ignorability equalities
fail because of baseline selection, p. 499 corrected comparison. -/
theorem baseline_selection_counterexample :
    FIV sixMass (liftUnit case2Unit) Prod.snd ∧
    fLatentIgnorability sixMass (liftUnit case2Unit) ∧
    fCE sixMass (fun i => (case2Unit i.1).y0)
      (fun i => (case2Unit i.1).receipt i.2 = true) = 1/2 ∧
    fCE sixMass (fun i => (case2Unit i.1).y0)
      (fun i => (case2Unit i.1).receipt i.2 = false) = 0 ∧
    fCE sixMass (fun i => (case2Unit i.1).y1)
      (fun i => (case2Unit i.1).receipt i.2 = true) = 3/2 ∧
    fCE sixMass (fun i => (case2Unit i.1).y1)
      (fun i => (case2Unit i.1).receipt i.2 = false) = 1 := by
  have ht : ValidLaw typeMass := by
    constructor
    · intro i; unfold typeMass; split <;> norm_num
    · norm_num [typeMass, Fin.sum_univ_succ]
  have hi := randomized_independent typeMass (1/2) ht
    (fun i => ((case2Unit i).x, (case2Unit i).d0, (case2Unit i).d1,
      (case2Unit i).y0, (case2Unit i).y1))
  have hv := randomized_valid typeMass (1/2) ht (by norm_num) (by norm_num)
  refine ⟨⟨hv, ?_, ?_, hi, ?_, ?_⟩, ?_, ?_⟩
  all_goals try norm_num [fCE, fE, fP, sixMass, liftUnit, randomized, typeMass,
    case2Unit, bit, PotentialUnit.receipt, PotentialUnit.defier,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  · rintro ⟨⟩ _
    norm_num [fCE, fE, fP, sixMass, liftUnit, randomized, typeMass, case2Unit,
      PotentialUnit.receipt, PotentialUnit.complier, PotentialUnit.tau,
      Fintype.sum_prod_type, Fin.sum_univ_succ]
  all_goals norm_num [fCE, fE, fP, sixMass, liftUnit, randomized, typeMass,
    case2Unit, bit, PotentialUnit.receipt, PotentialUnit.defier,
    Fintype.sum_prod_type, Fin.sum_univ_succ]

/- The P029-E004 witnesses use (C, tau, X), then independent H and Z. -/
abbrev Triple := Bool × Bool × Bool

/-- T3(A)'s eight-atom (C,τ,X) distribution. -/
def marginalMass (i : Triple) : ℝ :=
  if i.1 ∧ i.2.1 then (if i.2.2 then 3/16 else 1/16)
  else (if i.2.2 then 1/16 else 3/16)

/-- T3(B)'s eight-atom distribution. -/
def conditionalMass (i : Triple) : ℝ :=
  if i.1 = i.2.1 then
    (if i.1 = i.2.2 then 9/32 else 1/32)
  else 3/32

/-- Both T3 witnesses: A=(1-C)H, D₀=A, D₁=A+C, Y₀=0, Y₁=τ;
H is an independent Bernoulli(1/2) draw. -/
def independenceUnit (i : Triple × Bool) : PotentialUnit Bool :=
  ⟨i.1.2.2, (!i.1.1) && i.2, ((!i.1.1) && i.2) || i.1.1, 0, bit i.1.2.1⟩

def marginalJoint : (Triple × Bool) × Bool → ℝ :=
  randomized (randomized marginalMass (1/2)) (1/2)
def conditionalJoint : (Triple × Bool) × Bool → ℝ :=
  randomized (randomized conditionalMass (1/2)) (1/2)

/-- Independence conditional on a finite-valued covariate, T3(B). -/
def FCondIndep {L A B X : Type*} [Fintype L] (p : L → ℝ)
    (V : L → A) (W : L → B) (T : L → X) : Prop :=
  ∀ x a b, 0 < fP p (fun i => T i = x) →
    fP p (fun i => V i = a ∧ W i = b ∧ T i = x) / fP p (fun i => T i = x) =
    (fP p (fun i => V i = a ∧ T i = x) / fP p (fun i => T i = x)) *
    (fP p (fun i => W i = b ∧ T i = x) / fP p (fun i => T i = x))

/-- T3(A): heterogeneous effects are independent of the FULL compliance
type marginally; all five IV assumptions and overlap hold, but Assumption 1
fails at both profiles and the observed true-score ICSW ratio is 7/16 rather
than the ATE 1/2. This refutes the marginal reading on p. 499. -/
theorem marginal_independence_counterexample :
    FIV marginalJoint (liftUnit independenceUnit) Prod.snd ∧
    FIndep marginalJoint (fun i => i.1.1.2.1)
      (fun i => ((independenceUnit i.1).d0, (independenceUnit i.1).d1)) ∧
    fP marginalJoint (fun i => i.1.1.2.1 = true) = 1/2 ∧
    fP marginalJoint (fun i => i.1.1.2.1 = false) = 1/2 ∧
    fP marginalJoint (fun i => (independenceUnit i.1).x = false) = 5/8 ∧
    fP marginalJoint (fun i => (independenceUnit i.1).x = true) = 3/8 ∧
    fScore marginalJoint (liftUnit independenceUnit) false = 2/5 ∧
    fScore marginalJoint (liftUnit independenceUnit) true = 2/3 ∧
    (1/3 : ℝ) < fScore marginalJoint (liftUnit independenceUnit) false ∧
    (1/3 : ℝ) < fScore marginalJoint (liftUnit independenceUnit) true ∧
    fCE marginalJoint (fun i => (independenceUnit i.1).tau)
      (fun i => (independenceUnit i.1).x = false) = 2/5 ∧
    fCE marginalJoint (fun i => (independenceUnit i.1).tau)
      (fun i => (independenceUnit i.1).complier ∧ (independenceUnit i.1).x = false) = 1/4 ∧
    fCE marginalJoint (fun i => (independenceUnit i.1).tau)
      (fun i => (independenceUnit i.1).x = true) = 2/3 ∧
    fCE marginalJoint (fun i => (independenceUnit i.1).tau)
      (fun i => (independenceUnit i.1).complier ∧ (independenceUnit i.1).x = true) = 3/4 ∧
    fE marginalJoint (fun i => (independenceUnit i.1).tau) = 1/2 ∧
    fWald marginalJoint (liftUnit independenceUnit) Prod.snd (fun _ => 1) = 1/2 ∧
    fE marginalJoint (fun i => 1 / fScore marginalJoint (liftUnit independenceUnit)
      (independenceUnit i.1).x) = 17/8 ∧
    fWald marginalJoint (liftUnit independenceUnit) Prod.snd
      (fun i => 1 / fScore marginalJoint (liftUnit independenceUnit)
        (independenceUnit i.1).x) = 7/16 := by
  have ht : ValidLaw marginalMass := by
    constructor
    · rintro ⟨c,t,x⟩; cases c <;> cases t <;> cases x <;> norm_num [marginalMass]
    · norm_num [marginalMass, Fintype.sum_prod_type, Fintype.sum_bool]
  have hh := randomized_valid marginalMass (1/2) ht (by norm_num) (by norm_num)
  have hv := randomized_valid (randomized marginalMass (1/2)) (1/2) hh
    (by norm_num) (by norm_num)
  have hi := randomized_independent (randomized marginalMass (1/2)) (1/2) hh
    (fun i => ((independenceUnit i).x, (independenceUnit i).d0,
      (independenceUnit i).d1, (independenceUnit i).y0, (independenceUnit i).y1))
  refine ⟨⟨hv, ?_, ?_, hi, ?_, ?_⟩, ?_, ?_⟩
  all_goals try norm_num [fCE, fE, fP, fScore, fWald, marginalJoint,
    liftUnit, randomized, marginalMass, independenceUnit, bit,
    PotentialUnit.receipt, PotentialUnit.outcome, PotentialUnit.complier,
    PotentialUnit.defier, PotentialUnit.tau, Fintype.sum_prod_type, Fintype.sum_bool]
  · rintro t ⟨d0,d1⟩
    cases t <;> cases d0 <;> cases d1 <;>
      norm_num [fP, marginalJoint, randomized, marginalMass, independenceUnit,
        bit, Fintype.sum_prod_type, Fintype.sum_bool]
  all_goals norm_num [fCE, fE, fP, fScore, fWald, marginalJoint,
    liftUnit, randomized, marginalMass, independenceUnit, bit,
    PotentialUnit.receipt, PotentialUnit.outcome, PotentialUnit.complier,
    PotentialUnit.defier, PotentialUnit.tau, Fintype.sum_prod_type, Fintype.sum_bool]

/-- T3(B): effects and FULL type are independent given X, and Assumption 1
holds, but the observed unweighted IV ratio is 5/8 while the ATE and ICSW
ratio are 1/2. This refutes the conditional reading on p. 499. -/
theorem conditional_independence_counterexample :
    FIV conditionalJoint (liftUnit independenceUnit) Prod.snd ∧
    FCondIndep conditionalJoint (fun i => i.1.1.2.1)
      (fun i => ((independenceUnit i.1).d0, (independenceUnit i.1).d1))
      (fun i => (independenceUnit i.1).x) ∧
    fLatentIgnorability conditionalJoint (liftUnit independenceUnit) ∧
    fScore conditionalJoint (liftUnit independenceUnit) false = 1/4 ∧
    fScore conditionalJoint (liftUnit independenceUnit) true = 3/4 ∧
    (1/8 : ℝ) < fScore conditionalJoint (liftUnit independenceUnit) false ∧
    (1/8 : ℝ) < fScore conditionalJoint (liftUnit independenceUnit) true ∧
    fCE conditionalJoint (fun i => (independenceUnit i.1).tau)
      (fun i => (independenceUnit i.1).x = false) = 1/4 ∧
    fCE conditionalJoint (fun i => (independenceUnit i.1).tau)
      (fun i => (independenceUnit i.1).x = true) = 3/4 ∧
    fE conditionalJoint (fun i => (independenceUnit i.1).tau) = 1/2 ∧
    fE conditionalJoint (fun i => if (independenceUnit i.1).complier then
      (independenceUnit i.1).tau else 0) = 5/16 ∧
    fWald conditionalJoint (liftUnit independenceUnit) Prod.snd (fun _ => 1) = 5/8 ∧
    fWald conditionalJoint (liftUnit independenceUnit) Prod.snd
      (fun i => 1 / fScore conditionalJoint (liftUnit independenceUnit)
        (independenceUnit i.1).x) = 1/2 := by
  have ht : ValidLaw conditionalMass := by
    constructor
    · rintro ⟨c,t,x⟩; cases c <;> cases t <;> cases x <;> norm_num [conditionalMass]
    · norm_num [conditionalMass, Fintype.sum_prod_type, Fintype.sum_bool]
  have hh := randomized_valid conditionalMass (1/2) ht (by norm_num) (by norm_num)
  have hv := randomized_valid (randomized conditionalMass (1/2)) (1/2) hh
    (by norm_num) (by norm_num)
  have hi := randomized_independent (randomized conditionalMass (1/2)) (1/2) hh
    (fun i => ((independenceUnit i).x, (independenceUnit i).d0,
      (independenceUnit i).d1, (independenceUnit i).y0, (independenceUnit i).y1))
  refine ⟨⟨hv, ?_, ?_, hi, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals try norm_num [fCE, fE, fP, fScore, fWald, conditionalJoint,
    liftUnit, randomized, conditionalMass, independenceUnit, bit,
    PotentialUnit.receipt, PotentialUnit.outcome, PotentialUnit.complier,
    PotentialUnit.defier, PotentialUnit.tau, Fintype.sum_prod_type, Fintype.sum_bool]
  · rintro x t ⟨d0,d1⟩ _
    cases x <;> cases t <;> cases d0 <;> cases d1 <;>
      norm_num [fP, conditionalJoint, randomized, conditionalMass, independenceUnit,
        bit, Fintype.sum_prod_type, Fintype.sum_bool]
  · intro x _
    cases x <;> norm_num [fCE, fE, fP, conditionalJoint, liftUnit, randomized,
      conditionalMass, independenceUnit, bit, PotentialUnit.tau,
      PotentialUnit.complier, Fintype.sum_prod_type, Fintype.sum_bool]
  all_goals norm_num [fCE, fE, fP, fScore, fWald, conditionalJoint,
    liftUnit, randomized, conditionalMass, independenceUnit, bit,
    PotentialUnit.receipt, PotentialUnit.outcome, PotentialUnit.complier,
    PotentialUnit.defier, PotentialUnit.tau, Fintype.sum_prod_type, Fintype.sum_bool]

/- General probability statements: these are not restricted to finite atoms. -/

/-- The paper's Pr on a general probability space, pp. 494-495. -/
def mP {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) : ℝ :=
  (μ A).toReal

/-- Conditional mean on a positive-probability event, equation (3), p. 495.
This is a normalized restricted Bochner integral. -/
def mCE {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → ℝ)
    (A : Set Ω) : ℝ := (∫ ω in A, v ω ∂μ) / mP μ A

/-- The standing five IV assumptions, pp. 494-495, on an unrestricted
probability space. Randomization is joint independence from X and every
potential response; exclusion/SUTVA are the fixed response functions. -/
def IVAssumptions {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialUnit X) (Z : Ω → Bool) : Prop :=
  Measurable (fun ω => (U ω).x) ∧ Measurable (fun ω => (U ω).d0) ∧
  Measurable (fun ω => (U ω).d1) ∧ Measurable (fun ω => (U ω).y0) ∧
  Measurable (fun ω => (U ω).y1) ∧ Measurable Z ∧
  Integrable (fun ω => (U ω).y0) μ ∧ Integrable (fun ω => (U ω).y1) μ ∧
  IndepFun Z (fun ω => ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1)) μ ∧
  0 < mP μ {ω | Z ω = true} ∧ mP μ {ω | Z ω = true} < 1 ∧
  μ {ω | (U ω).defier} = 0 ∧
  mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = true} -
    mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = false} ≠ 0

/-- Assumption 1 at a covariate profile, p. 499. -/
def latentAt {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialUnit X) (x : X) : Prop :=
  mCE μ (fun ω => (U ω).tau) {ω | (U ω).x = x} =
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier ∧ (U ω).x = x}

/-- The displayed received-treatment ignorability condition (I), p. 499. -/
def typicalAt {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialUnit X) (Z : Ω → Bool) (x : X) : Prop :=
  mCE μ (fun ω => (U ω).y0) {ω | (U ω).receipt (Z ω) = true ∧ (U ω).x = x} =
    mCE μ (fun ω => (U ω).y0) {ω | (U ω).receipt (Z ω) = false ∧ (U ω).x = x} ∧
  mCE μ (fun ω => (U ω).y1) {ω | (U ω).receipt (Z ω) = true ∧ (U ω).x = x} =
    mCE μ (fun ω => (U ω).y1) {ω | (U ω).receipt (Z ω) = false ∧ (U ω).x = x}

/-- Compliance score for a positive-probability profile, p. 496. -/
def scoreAt {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialUnit X) (x : X) : ℝ :=
  mP μ {ω | (U ω).complier ∧ (U ω).x = x} / mP μ {ω | (U ω).x = x}

/-- Complier effect at a covariate profile, p. 499. -/
def complierAt {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialUnit X) (x : X) : ℝ :=
  mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier ∧ (U ω).x = x}

/-- Population weighted arm mean, Section 3.3, p. 498. -/
def mArm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → Bool)
    (w v : Ω → ℝ) (z : Bool) : ℝ :=
  mCE μ (fun ω => w ω * v ω) {ω | Z ω = z} / mCE μ w {ω | Z ω = z}

/-- Population weighted Wald ratio, Section 3.3, p. 498. -/
def mWald {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialUnit X) (Z : Ω → Bool) (w : Ω → ℝ) : ℝ :=
  (mArm μ Z w (fun ω => (U ω).outcome (Z ω)) true -
    mArm μ Z w (fun ω => (U ω).outcome (Z ω)) false) /
  (mArm μ Z w (fun ω => bit ((U ω).receipt (Z ω))) true -
    mArm μ Z w (fun ω => bit ((U ω).receipt (Z ω))) false)

/-- General covariance used by the corrected population limit comparison. -/
def mCov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (u v : Ω → ℝ) : ℝ :=
  (∫ ω, u ω * v ω ∂μ) - (∫ ω, u ω ∂μ) * (∫ ω, v ω ∂μ)

/-- Random assignment, p. 495: "Zᵢ is randomly assigned" with probability
e. This is the actual Bernoulli measure on the two assignment values. -/
def bernoulliMeasure (e : ℝ) : Measure Bool :=
  ENNReal.ofReal e • Measure.dirac true + ENNReal.ofReal (1-e) • Measure.dirac false

/-- T25, a probability-law lemma for the standing random-assignment
assumption: Bernoulli assignment has total mass one for 0≤e≤1. -/
theorem bernoulli_measure_probability (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    IsProbabilityMeasure (bernoulliMeasure e) := by
  have hs : ENNReal.ofReal e + ENNReal.ofReal (1-e) = 1 := by
    rw [← ENNReal.ofReal_add he0 (sub_nonneg.mpr he1)]
    norm_num
  constructor
  simpa [bernoulliMeasure] using hs

/-- The paper's general population and random assignment, pp. 494-495.
μX is the covariate law, and the Markov kernel κ(x) is the actual probability
law of units conditional on X=x. Composition followed by independent
Bernoulli assignment forms the population law; no finite-support condition
or free conditional-mean functions are substituted. -/
def kernelPopulationLaw {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μX : Measure X) (κ : Kernel X Ω) (e : ℝ) : Measure ((X × Ω) × Bool) :=
  (μX.compProd κ).prod (bernoulliMeasure e)

/-- Potential responses of the unit in the composed population law.
The same PotentialUnit objects of p. 494 are used; the first coordinate
records its covariate profile and the final Bool its assignment. -/
def kernelPopulationUnit {Ω X : Type*} (U : Ω → PotentialUnit X) :
    ((X × Ω) × Bool) → PotentialUnit X := fun i => U i.1.2


/-- Bernoulli likelihood contribution, equation (7), p. 497; natural powers
implement the printed 0^0=1 closure convention. -/
def bernoulliFactor (p : ℝ) (d : Bool) : ℝ :=
  p ^ (if d then 1 else 0 : ℕ) * (1 - p) ^ (if d then 0 else 1 : ℕ)

/-- Receipt probability in the nested model, equation (7), p. 497. -/
def nestedReceipt (a b : ℝ) (z : Bool) : ℝ := a * (1 - b) * bit z + a * b

/-- The package's printed objective -Σ log(Lᵢwᵢ), R/compliance.score.R,
lines 88-91; this is code, not an equation of the 2013 article. -/
def packageObjective {I : Type*} [Fintype I] (L w : I → ℝ) : ℝ :=
  -(∑ i, Real.log (L i * w i))

/-- Corrected observation-weighted negative log likelihood -Σ wᵢlog Lᵢ,
T8 (P029-E016 and P029-E014). A zero observation weight contributes zero. -/
def weightedObjective {I : Type*} [Fintype I] (L w : I → ℝ) : ℝ :=
  -(∑ i, w i * Real.log (L i))

/-- Exact minimizer of an objective, used to state the package's claim
without making claims about a stochastic numerical optimizer. -/
def IsMinimizer {Θ : Type*} (Q : Θ → ℝ) (θ : Θ) : Prop := ∀ t, Q θ ≤ Q t

/-- T7(i): positive weights INSIDE the logarithm only add a parameter-free
constant. This is the exact defect in the package's two-sided fit. -/
theorem inside_log_weights_identity {I : Type*} [Fintype I]
    (L w : I → ℝ) (hL : ∀ i, 0 < L i) (hw : ∀ i, 0 < w i) :
    packageObjective L w = packageObjective L (fun _ => 1) - ∑ i, Real.log (w i) := by
  unfold packageObjective
  simp only [mul_one]
  simp_rw [Real.log_mul (ne_of_gt (hL _)) (ne_of_gt (hw _))]
  rw [Finset.sum_add_distrib]
  ring

/-- T7(i): the complete set of exact minimizers is invariant to every vector
of positive weights. Re-executing this fit cannot implement a weighted bootstrap. -/
theorem inside_log_minimizers {I Θ : Type*} [Fintype I]
    (L : Θ → I → ℝ) (w : I → ℝ) (hL : ∀ θ i, 0 < L θ i)
    (hw : ∀ i, 0 < w i) (θ : Θ) :
    IsMinimizer (fun t => packageObjective (L t) w) θ ↔
      IsMinimizer (fun t => weightedObjective (L t) (fun _ => 1)) θ := by
  have h : ∀ t, packageObjective (L t) w =
      weightedObjective (L t) (fun _ => 1) - ∑ i, Real.log (w i) := by
    intro t
    simpa [weightedObjective, packageObjective] using
      inside_log_weights_identity (L t) w (hL t) hw
  simp only [IsMinimizer, h, sub_le_sub_iff_right]

/-- Negative log at zero must be +∞ (R's convention). Real.log 0 in Lean is
totalized to 0, so the zero-weight bug is explicitly stated with EReal. -/
def extendedNegLog (x : ℝ) : EReal := if x = 0 then ⊤ else (-Real.log x : ℝ)

/-- Extended-real version of the package's -Σ log(Lᵢwᵢ), T7(ii),
R/compliance.score.R lines 88-91. This retains the R value +∞ at zero. -/
def extendedPackageObjective {I : Type*} [Fintype I] (L w : I → ℝ) : EReal :=
  ∑ i, extendedNegLog (L i*w i)

/-- T7(ii): at a zero weight the likelihood product is zero and its negative
log contribution is infinite, despite a positive unclipped likelihood. -/
theorem zero_weight_infinite_contribution (L : ℝ) :
    L * 0 = 0 ∧ extendedNegLog (L * 0) = ⊤ := by
  simp [extendedNegLog]

/-- T7(ii), full objective: if any observation has zero weight, every
parameter value has objective +∞; finite other contributions cannot cancel it.
The clipped positive likelihood and positive other weights are retained. -/
theorem zero_weight_objective_infinite {I : Type*} [Fintype I]
    (L w : I → ℝ) (hL : ∀ j, L j ∈ Ioc (0 : ℝ) 1) (i : I)
    (hi : w i = 0) (hw : ∀ j, j ≠ i → 0 < w j) :
    extendedPackageObjective L w = ⊤ := by
  classical
  have hsum (s : Finset I) : (∑ j ∈ s, extendedNegLog (L j*w j)) ≠ ⊥ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, EReal.add_ne_bot_iff]
      refine ⟨?_, ih⟩
      unfold extendedNegLog
      split_ifs <;> simp
  unfold extendedPackageObjective
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [hi, mul_zero, extendedNegLog, if_pos rfl]
  exact EReal.top_add_of_ne_bot (hsum _)

/-- T8(a): zero-weight observations contribute zero and unit weights give
the ordinary negative log likelihood. This applies to nonnegative finite weights. -/
theorem corrected_objective_zero_unit {I : Type*} [Fintype I]
    (L : I → ℝ) (i : I) :
    (0 : ℝ) * Real.log (L i) = 0 ∧
    weightedObjective L (fun _ => 1) = packageObjective L (fun _ => 1) := by
  simp [weightedObjective, packageObjective]

/-- T8(a): for integer observation weights, exp(-Qw) is exactly the
likelihood of repeating each observation wᵢ times, not of multiplying it by wᵢ. -/
theorem integer_weight_replication {I : Type*} [Fintype I]
    (L : I → ℝ) (w : I → ℕ) (hL : ∀ i, 0 < L i) :
    Real.exp (-weightedObjective L (fun i => (w i : ℝ))) = ∏ i, (L i) ^ w i := by
  simp only [weightedObjective, neg_neg]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.exp_nat_mul, Real.exp_log (hL i)]

/-- Weighted Bernoulli cell log likelihood, used in the T7/T8 saturation
argument: S is the sum of success weights and F the sum of failure weights. -/
def cellLog (S F q : ℝ) : ℝ := S * Real.log q + F * Real.log (1 - q)

/-- T8(b): a cell with positive success and failure weight totals has unique
maximum at q=S/(S+F). The proof uses log u≤u-1, including strictness. -/
theorem weighted_cell_unique_max (S F : ℝ) (hS : 0 < S) (hF : 0 < F) :
    (S / (S + F)) ∈ Ioo (0 : ℝ) 1 ∧
    ∀ q ∈ Ioo (0 : ℝ) 1,
      cellLog S F q ≤ cellLog S F (S / (S + F)) ∧
      (cellLog S F q = cellLog S F (S / (S + F)) ↔ q = S / (S + F)) := by
  let a := S / (S + F)
  have hSF : 0 < S + F := by linarith
  have ha : 0 < a := div_pos hS hSF
  have ha1 : a < 1 := (div_lt_one hSF).2 (by linarith)
  have hca : 0 < 1 - a := by linarith
  refine ⟨⟨ha, ha1⟩, ?_⟩
  intro q hq
  have hcq : 0 < 1 - q := by linarith [hq.2]
  have hlog : cellLog S F q - cellLog S F a =
      S * Real.log (q / a) + F * Real.log ((1 - q) / (1 - a)) := by
    rw [Real.log_div (ne_of_gt hq.1) (ne_of_gt ha),
      Real.log_div (ne_of_gt hcq) (ne_of_gt hca)]
    unfold cellLog
    ring
  have hlin : S * (q / a - 1) + F * ((1 - q) / (1 - a) - 1) = 0 := by
    have hcomp : 1 - a = F / (S + F) := by dsimp [a]; field_simp [hSF.ne'] <;> ring
    rw [hcomp]
    dsimp [a]
    field_simp [hSF.ne', hS.ne', hF.ne'] <;> ring
  have h1 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hq.1 ha)) hS.le
  have h2 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hcq hca)) hF.le
  have hle : cellLog S F q ≤ cellLog S F a := by linarith
  refine ⟨hle, ?_⟩
  constructor
  · intro heq
    by_contra hne
    have hratio : q / a ≠ 1 := by
      intro h
      apply hne
      exact (div_eq_one_iff_eq (ne_of_gt ha)).1 h
    have hs := mul_lt_mul_of_pos_left
      (Real.log_lt_sub_one_of_pos (div_pos hq.1 ha) hratio) hS
    linarith
  · intro heq; rw [heq]

/-- T8(b): the weighted cell log likelihood is strictly concave on (0,1).
This is stated separately from its unique-maximizer theorem. -/
theorem weighted_cell_strict_concavity (S F : ℝ) (hS : 0 < S) (hF : 0 < F) :
    StrictConcaveOn ℝ (Ioo (0 : ℝ) 1) (cellLog S F) := by
  refine ⟨convex_Ioo 0 1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have h1 := strictConcaveOn_log_Ioi.2 hx.1 hy.1 hxy ha hb hab
  have hxy' : (1-x : ℝ) ≠ 1-y := by intro h; apply hxy; linarith
  have h2 := strictConcaveOn_log_Ioi.2
    (show (1-x : ℝ) ∈ Ioi 0 by exact sub_pos.mpr hx.2)
    (show (1-y : ℝ) ∈ Ioi 0 by exact sub_pos.mpr hy.2) hxy' ha hb hab
  simp only [smul_eq_mul] at h1 h2 ⊢
  have heq : a*(1-x)+b*(1-y) = 1-(a*x+b*y) := by nlinarith
  rw [heq] at h2
  have h1' := mul_lt_mul_of_pos_left h1 hS
  have h2' := mul_lt_mul_of_pos_left h2 hF
  unfold cellLog
  nlinarith

/-- Success-weight total S_c, T8(b): sum of observation
weights in cell c over observations with D=1. -/
def cellSuccessWeight {I C : Type*} [Fintype I] (cell : I → C) (D : I → Bool)
    (w : I → ℝ) (c : C) : ℝ := ∑ i, if cell i = c ∧ D i = true then w i else 0

/-- Failure-weight total F_c, T8(b): sum of observation
weights in cell c over observations with D=0. -/
def cellFailureWeight {I C : Type*} [Fintype I] (cell : I → C) (D : I → Bool)
    (w : I → ℝ) (c : C) : ℝ := ∑ i, if cell i = c ∧ D i = false then w i else 0

/-- T8(b), full saturated likelihood consequence: when every cell has
positive success and failure weight totals, the actual observation-weighted
objective has unique minimizer q_c=S_c/(S_c+F_c) over free interior cell rates. -/
theorem saturated_weighted_objective_minimum {I C : Type*} [Fintype I] [Fintype C]
    (cell : I → C) (D : I → Bool) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hS : ∀ c, 0 < cellSuccessWeight cell D w c)
    (hF : ∀ c, 0 < cellFailureWeight cell D w c) :
    let qhat := fun c => cellSuccessWeight cell D w c /
      (cellSuccessWeight cell D w c + cellFailureWeight cell D w c)
    (∀ c, qhat c ∈ Ioo (0 : ℝ) 1) ∧
    ∀ q : C → ℝ, (∀ c, q c ∈ Ioo (0 : ℝ) 1) →
      weightedObjective (fun i => bernoulliFactor (qhat (cell i)) (D i)) w ≤
        weightedObjective (fun i => bernoulliFactor (q (cell i)) (D i)) w ∧
      (weightedObjective (fun i => bernoulliFactor (qhat (cell i)) (D i)) w =
        weightedObjective (fun i => bernoulliFactor (q (cell i)) (D i)) w ↔ q = qhat) := by
  classical
  let qhat : C → ℝ := fun c => cellSuccessWeight cell D w c /
    (cellSuccessWeight cell D w c + cellFailureWeight cell D w c)
  change (∀ c, qhat c ∈ Ioo (0 : ℝ) 1) ∧
    ∀ q : C → ℝ, (∀ c, q c ∈ Ioo (0 : ℝ) 1) →
      weightedObjective (fun i => bernoulliFactor (qhat (cell i)) (D i)) w ≤
        weightedObjective (fun i => bernoulliFactor (q (cell i)) (D i)) w ∧
      (weightedObjective (fun i => bernoulliFactor (qhat (cell i)) (D i)) w =
        weightedObjective (fun i => bernoulliFactor (q (cell i)) (D i)) w ↔ q = qhat)
  have hSuccess (q : C → ℝ) :
      (∑ c, cellSuccessWeight cell D w c * Real.log (q c)) =
        ∑ i, if D i = true then w i * Real.log (q (cell i)) else 0 := by
    unfold cellSuccessWeight
    simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hd : D i = true <;> simp [hd, eq_comm]
  have hFailure (q : C → ℝ) :
      (∑ c, cellFailureWeight cell D w c * Real.log (1-q c)) =
        ∑ i, if D i = false then w i * Real.log (1-q (cell i)) else 0 := by
    unfold cellFailureWeight
    simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hd : D i = false <;> simp [hd, eq_comm]
  have hdecomp (q : C → ℝ) :
      weightedObjective (fun i => bernoulliFactor (q (cell i)) (D i)) w =
        -(∑ c, cellLog (cellSuccessWeight cell D w c)
          (cellFailureWeight cell D w c) (q c)) := by
    calc
      _ = -((∑ i, if D i = true then w i*Real.log (q (cell i)) else 0) +
          (∑ i, if D i = false then w i*Real.log (1-q (cell i)) else 0)) := by
        unfold weightedObjective
        rw [← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        by_cases hd : D i = true
        · simp [bernoulliFactor,hd]
        · have hf : D i = false := Bool.eq_false_of_not_eq_true hd
          simp [bernoulliFactor,hd,hf]
      _ = -((∑ c, cellSuccessWeight cell D w c*Real.log (q c)) +
          (∑ c, cellFailureWeight cell D w c*Real.log (1-q c))) := by
        rw [hSuccess q,hFailure q]
      _ = _ := by simp only [cellLog,Finset.sum_add_distrib]
  have hmax (c : C) := weighted_cell_unique_max
    (cellSuccessWeight cell D w c) (cellFailureWeight cell D w c) (hS c) (hF c)
  constructor
  · intro c; exact (hmax c).1
  · intro q hq
    simp only [hdecomp qhat,hdecomp q]
    have hle (c : C) :
        cellLog (cellSuccessWeight cell D w c) (cellFailureWeight cell D w c) (q c) ≤
          cellLog (cellSuccessWeight cell D w c) (cellFailureWeight cell D w c) (qhat c) :=
      ((hmax c).2 (q c) (hq c)).1
    refine ⟨neg_le_neg (Finset.sum_le_sum (fun c _ => hle c)),?_⟩
    constructor
    · intro heq
      have hz : (∑ c, (cellLog (cellSuccessWeight cell D w c)
            (cellFailureWeight cell D w c) (qhat c) -
          cellLog (cellSuccessWeight cell D w c) (cellFailureWeight cell D w c) (q c))) = 0 := by
        rw [Finset.sum_sub_distrib]
        linarith
      apply funext
      intro c
      have ht := (Finset.sum_eq_zero_iff_of_nonneg
        (fun c _ => sub_nonneg.mpr (hle c))).1 hz c (Finset.mem_univ c)
      exact ((hmax c).2 (q c) (hq c)).2.mp (by linarith)
    · intro heq; rw [heq]

/-- T8(d): for a common positive weight k, both criteria have exactly the
unweighted minimizers. Nonconstant weights need not have this property. -/
theorem constant_weight_minimizers {I Θ : Type*} [Fintype I]
    (L : Θ → I → ℝ) (hL : ∀ θ i, 0 < L θ i) (k : ℝ) (hk : 0 < k) (θ : Θ) :
    IsMinimizer (fun t => packageObjective (L t) (fun _ => k)) θ ↔
      IsMinimizer (fun t => weightedObjective (L t) (fun _ => k)) θ := by
  have hscale : ∀ t, weightedObjective (L t) (fun _ => k) =
      k * weightedObjective (L t) (fun _ => 1) := by
    intro t; simp [weightedObjective, ← Finset.mul_sum]
  rw [inside_log_minimizers L (fun _ => k) hL (fun _ => hk)]
  simp only [IsMinimizer, hscale, mul_le_mul_iff_right₀ hk]

/-- T7(iii): the exact sixteen-row one-sided sample (W,Z,k), with four rows
per (W,Z), one treated success at W=0 and three at W=1. -/
def oneSidedSample (i : Bool × Bool × Fin 4) : PotentialUnit Bool :=
  ⟨i.1, false, decide (i.2.2.val < if i.1 then 3 else 1), 0, 1 + bit i.1⟩
def sampleZ (i : Bool × Bool × Fin 4) : Bool := i.2.1
def oneSidedWeight (i : Bool × Bool × Fin 4) : ℝ :=
  if (oneSidedSample i).receipt (sampleZ i) then 9 else 1
def unweightedScores (x : Bool) : ℝ := if x then 3/4 else 1/4
def correctedScores (x : Bool) : ℝ := if x then 27/28 else 3/4

/-- T7(iii)/T8(c): weighted score fitting changes the actual observed weighted
Wald estimate from 3/2 to 17/10 on the explicit sixteen observations. The
scores are the cell maximizers with totals (9,3) and (27,1). -/
theorem weighted_score_counterexample :
    (9 / (9 + 3) : ℝ) = correctedScores false ∧
    (27 / (27 + 1) : ℝ) = correctedScores true ∧
    fWald (fun _ : Bool × Bool × Fin 4 => 1/16) oneSidedSample sampleZ
      (fun i => oneSidedWeight i / unweightedScores i.1) = 3/2 ∧
    fWald (fun _ : Bool × Bool × Fin 4 => 1/16) oneSidedSample sampleZ
      (fun i => oneSidedWeight i / correctedScores i.1) = 17/10 ∧
    (3/2 : ℝ) ≠ 17/10 := by
  norm_num [fWald, fCE, fE, fP, oneSidedSample, sampleZ, oneSidedWeight,
    unweightedScores, correctedScores, PotentialUnit.outcome, PotentialUnit.receipt,
    bit, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]

/-- T7(iv): four (W,Z) cells each contain four observations. -/
def twoSidedSuccesses (i : Bool × Bool) : ℕ := if i.2 then (if i.1 then 3 else 2) else 1
def packageCells (i : Bool × Bool) : ℝ := if i.2 then (if i.1 then 3/4 else 1/2) else 1/4
def weightedCells (i : Bool × Bool) : ℝ := if i.2 then (if i.1 then 27/28 else 9/10) else 3/4
def twoSidedLikelihood (q : Bool × Bool → ℝ) : ℝ :=
  ∏ i, q i ^ twoSidedSuccesses i * (1 - q i) ^ (4 - twoSidedSuccesses i)

/-- T7(iv)/T8(c): both cell vectors are feasible nested probabilities; the
unweighted likelihood at the weighted fit divided by that at the package fit
is 729/1500625<1, and their compliance scores differ. -/
theorem two_sided_weight_counterexample :
    (∀ x, 0 < packageCells (x,false) ∧ packageCells (x,false) < packageCells (x,true) ∧
      packageCells (x,true) < 1) ∧
    (∀ x, 0 < weightedCells (x,false) ∧ weightedCells (x,false) < weightedCells (x,true) ∧
      weightedCells (x,true) < 1) ∧
    twoSidedLikelihood weightedCells / twoSidedLikelihood packageCells = 729/1500625 ∧
    (729/1500625 : ℝ) < 1 ∧
    weightedCells (false,true) - weightedCells (false,false) = 3/20 ∧
    weightedCells (true,true) - weightedCells (true,false) = 3/14 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x; cases x <;> norm_num [packageCells]
  · intro x; cases x <;> norm_num [weightedCells]
  · norm_num [twoSidedLikelihood, twoSidedSuccesses, weightedCells,
      packageCells, Fintype.prod_prod_type, Fintype.prod_bool]

/-- T7(v): the refitted bootstrap slope (t+11)/(t+7) has nonzero derivative
-1/16 at t=1. With scores fixed, the slope is the constant 3/2. -/
theorem bootstrap_first_step_derivative :
    HasDerivAt (fun t : ℝ => (t + 11) / (t + 7)) (-1/16) 1 ∧
    HasDerivAt (fun _ : ℝ => (3/2 : ℝ)) 0 1 := by
  constructor
  · convert ((hasDerivAt_id (1 : ℝ)).add_const 11).div
      ((hasDerivAt_id (1 : ℝ)).add_const 7) (by norm_num : (1 : ℝ) + 7 ≠ 0) using 1 <;>
      first | rfl | norm_num
  · exact hasDerivAt_const _ _


/-- RMSE over R replicates, supplement A5/A7, T6(b)/T22. The supplement
prints no formula; this is the mathematical meaning of "RMSE". -/
def rmse {R : ℕ} (t benchmark : Fin R → ℝ) : ℝ :=
  Real.sqrt ((∑ r, (t r - benchmark r) ^ 2) / R)

/-- The companion heterogeneous-design benchmark actually used by the code,
T5: mean of 5(1+X1+X2+X3), supplement A1 and the deposited Noise script. -/
def heterogeneousBenchmark {n : ℕ} (x : Fin n → Fin 3 → ℝ) : ℝ :=
  (∑ i, 5 * (1 + x i 0 + x i 1 + x i 2)) / n

/-- T6(a): a homogeneous treatment effect 5 gives sample average effect 5
for EVERY nonempty sample, not the companion heterogeneous sample benchmark. -/
theorem homogeneous_sample_effect (n : ℕ) (hn : 0 < n) (Y0 : Fin n → ℝ) :
    (∑ i, ((Y0 i + 5) - Y0 i)) / (n : ℝ) = 5 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [hnR]

/-- T6(a): population ATE and LATE equal 5 for the homogeneous design,
on an arbitrary probability space and a positive-probability complier event. -/
theorem homogeneous_population_effect {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y0 : Ω → ℝ)
    (C : Set Ω) (hC : MeasurableSet C) (hc : 0 < mP μ C) :
    (∫ ω, ((Y0 ω + 5) - Y0 ω) ∂μ) = 5 ∧
    mCE μ (fun ω => (Y0 ω + 5) - Y0 ω) C = 5 := by
  have hv : (fun ω => (Y0 ω + 5) - Y0 ω) = fun _ => (5 : ℝ) := by
    funext ω; ring
  rw [hv]
  constructor
  · simp
  · have hcn : (μ C).toReal ≠ 0 := ne_of_gt hc
    simp [mCE, mP, Measure.real, hcn]

/-- T6(b)/T22: the homogeneous-noise RMSE is scored against the true effect
5 in each of 2500 replicates; no historical numerical entries are asserted. -/
theorem homogeneous_rmse_rule (t : Fin 2500 → ℝ) :
    rmse t (fun _ => 5) = Real.sqrt ((∑ r, (t r - 5) ^ 2) / 2500) := by
  rfl

/-- T6(d): the exact squared-error discrepancy has a cross term whose sign
need not vanish. This explains why adding 25/n is not a table correction. -/
theorem squared_error_discrepancy (t B : ℝ) :
    (t - B)^2 - (t - 5)^2 = (B - 5)^2 - 2 * (t - 5) * (B - 5) := by
  ring

/-- T6(d): the same exact relation holds for every finite simulation run. -/
theorem finite_run_mse_discrepancy {R : ℕ} (t B : Fin R → ℝ) :
    (∑ r, (t r - B r)^2) / R - (∑ r, (t r - 5)^2) / R =
      (∑ r, (B r - 5)^2) / R - (2 / R) * ∑ r, (t r - 5) * (B r - 5) := by
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp_rw [squared_error_discrepancy, mul_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- T6(d): finite probability expectations give Var(B)-2Cov(t,B) whenever
E(B)=5. This is the exact moment lemma, before any asymptotic approximation. -/
theorem finite_expected_mse_discrepancy {L : Type*} [Fintype L]
    (p t B : L → ℝ) (hp : ValidLaw p) (hB : fE p B = 5) :
    fE p (fun i => (t i - B i)^2) - fE p (fun i => (t i - 5)^2) =
      fVar p B - 2 * fCov p t B := by
  unfold fVar fCov fE at *
  have hpoly : ∀ i, p i * (t i - B i)^2 - p i * (t i - 5)^2 =
      p i * (B i * B i) - 2 * (p i * (t i * B i)) +
      10 * (p i * t i) - 25 * p i := by intro i; ring
  rw [← Finset.sum_sub_distrib]
  simp_rw [hpoly]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    hp.2, hB]
  ring

/-- T6(d), general second-moment version, allowing continuous random variables. -/
theorem expected_mse_discrepancy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t B : Ω → ℝ)
    (ht : MemLp t 2 μ) (hB2 : MemLp B 2 μ) (hB : (∫ ω, B ω ∂μ) = 5) :
    (∫ ω, (t ω - B ω)^2 ∂μ) - (∫ ω, (t ω - 5)^2 ∂μ) =
      mCov μ B B - 2 * mCov μ t B := by
  have hti : Integrable t μ := ht.integrable (by norm_num)
  have hprod : Integrable (fun ω => t ω*B ω) μ := ht.integrable_mul hB2
  have hdiff : Integrable (fun ω => (t ω-B ω)^2) μ := (ht.sub hB2).integrable_sq
  have hdiff5 : Integrable (fun ω => (t ω-5)^2) μ :=
    (ht.sub (memLp_const (5 : ℝ))).integrable_sq
  have hpoly : (fun ω => (t ω-B ω)^2-(t ω-5)^2) =
      (fun ω => B ω^2-2*(t ω*B ω)+10*t ω-25) := by
    funext ω; ring
  rw [← integral_sub hdiff hdiff5, hpoly,
    integral_sub (f := fun ω => B ω^2-2*(t ω*B ω)+10*t ω) (g := fun _ => 25)
      ((hB2.integrable_sq.sub (hprod.const_mul 2)).add (hti.const_mul 10))
      (integrable_const (25 : ℝ)),
    integral_add (f := fun ω => B ω^2-2*(t ω*B ω)) (g := fun ω => 10*t ω)
      (hB2.integrable_sq.sub (hprod.const_mul 2)) (hti.const_mul 10),
    integral_sub (f := fun ω => B ω^2) (g := fun ω => 2*(t ω*B ω))
      hB2.integrable_sq (hprod.const_mul 2),
    integral_const_mul, integral_const_mul]
  simp [mCov, pow_two, hB] <;> ring

/-- T6(c): uniform(-1,1) covariates, represented by the actual normalized
Lebesgue distribution (not an arbitrary law with matching moments). -/
def uniformMinusOneOne : Measure ℝ :=
  ProbabilityTheory.cond volume (Ioo (-1 : ℝ) 1)

/-- T6(c): exact uniform first and second moments used in the benchmark variance. -/
theorem uniform_covariate_moments :
    (∫ u, u ∂uniformMinusOneOne) = 0 ∧
    (∫ u, u^2 ∂uniformMinusOneOne) = 1/3 := by
  constructor
  · unfold uniformMinusOneOne ProbabilityTheory.cond
    rw [integral_smul_measure, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_id]
    norm_num [Real.volume_Ioo]
  · unfold uniformMinusOneOne ProbabilityTheory.cond
    rw [integral_smul_measure, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_pow]
    norm_num [Real.volume_Ioo]


/-- T5: five observed-noise profiles, each paired with Z=0 and Z=1 and
repeated 50 times. -/
def noiseProfile (k : Fin 5) : Fin 3 → ℝ :=
  if k.val = 0 then ![0,0,0] else
  if k.val = 1 then ![1/2,0,0] else
  if k.val = 2 then ![0,1/2,0] else
  if k.val = 3 then ![0,0,1/2] else ![-1/2,-1/2,-1/2]

abbrev RMSEIndex := Fin 50 × Fin 5 × Bool

/-- T5 instrument/regressor matrix Q=[1,Z,W1,W2,W3] (the two are identical
because all 500 realized units are compliers and D=Z). -/
def rmseQ : Matrix RMSEIndex (Fin 5) ℝ :=
  fun i => ![1, bit i.2.2, noiseProfile i.2.1 0, noiseProfile i.2.1 1, noiseProfile i.2.1 2]

def rmseGram : Matrix (Fin 5) (Fin 5) ℝ :=
  !![500,250,0,0,0; 250,250,0,0,0; 0,0,50,25,25; 0,0,25,50,25; 0,0,25,25,50]

/-- T5's two explicit homogeneous potential-outcome inputs:
"Y₀ᵢ=5+εᵞᵢ", "Y2ᵢ=Y₀ᵢ+5Dᵢ". The fixed realized noise is zero in
the perfect input and the stored assignment bit in the opposite input.
Both have D₀=0,D₁=1 and a potential treatment effect exactly 5. -/
def rmseHomogeneousUnit (opposite : Bool) (i : RMSEIndex) : PotentialUnit (Fin 3 → ℝ) :=
  let y0 := 5 + (if opposite then bit i.2.2 else 0)
  ⟨noiseProfile i.2.1, false, true, y0, y0+5⟩

/-- T5(a): actual cross-products of the 500-row design have the displayed
Gram matrix. The repetition is counted exactly, without a numerical fit. -/
theorem rmse_design_gram : rmseQ.transpose * rmseQ = rmseGram := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type, rmseQ]
  all_goals
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num [rmseGram, noiseProfile, bit, Fintype.sum_bool, Fin.sum_univ_succ]

/-- T5(a): the exact nonzero determinant guarantees that the actual 2SLS
normal equations identify a coefficient, rather than assigning an arbitrary t. -/
theorem rmse_design_determinant : rmseGram.det = 3906250000 := by
  norm_num [rmseGram, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.det_fin_two, Matrix.submatrix, Fin.succAbove, Fin.sum_univ_succ]

/-- Exact recovery from a nonsingular normal-equation matrix; when regressors
equal instruments this is the 2SLS second-stage coefficient used in T5. -/
theorem normal_equation_exact_recovery {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℝ) (b : n → ℝ) (hG : IsUnit G.det) :
    G⁻¹.mulVec (G.mulVec b) = b := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hG, Matrix.one_mulVec]

/-- T5(b)-(c): the exact two outcomes are Q(5,5,0,0,0) and Q(5,6,0,0,0),
while the homogeneous potential effect is 5 in BOTH inputs. -/
theorem rmse_witness_outcomes :
    (∀ i : RMSEIndex, rmseQ.mulVec ![5,5,0,0,0] i = 5 + 5 * bit i.2.2) ∧
    (∀ i : RMSEIndex, rmseQ.mulVec ![5,6,0,0,0] i = 5 + 6 * bit i.2.2) ∧
    heterogeneousBenchmark (fun _ : Fin 500 => ![1/5,0,0]) = 6 := by
  constructor
  · intro i; simp [Matrix.mulVec, dotProduct, rmseQ, Fin.sum_univ_succ] <;> ring
  constructor
  · intro i; simp [Matrix.mulVec, dotProduct, rmseQ, Fin.sum_univ_succ] <;> ring
  · norm_num [heterogeneousBenchmark, Finset.sum_const]

/-- T5 counterexample: the coefficients of the actual nonsingular 2SLS
design are 5 and 6; scoring them about the companion benchmark 6 instead
of the true effect 5 reverses the squared-error discrepancy's sign. -/
theorem homogeneous_rmse_counterexample :
    rmseQ.transpose * rmseQ = rmseGram ∧
    (∀ opposite i, (rmseHomogeneousUnit opposite i).tau = 5 ∧
      (rmseHomogeneousUnit opposite i).receipt i.2.2 = i.2.2 ∧
      (rmseHomogeneousUnit opposite i).outcome i.2.2 =
        5 + (if opposite then 6 else 5) * bit i.2.2) ∧
    heterogeneousBenchmark (fun _ : Fin 500 => ![1/5,0,0]) = 6 ∧
    rmseGram⁻¹.mulVec (rmseGram.mulVec ![5,5,0,0,0]) = ![5,5,0,0,0] ∧
    rmseGram⁻¹.mulVec (rmseGram.mulVec ![5,6,0,0,0]) = ![5,6,0,0,0] ∧
    ((5 - 6 : ℝ)^2 = 1 ∧ (5 - 5 : ℝ)^2 = 0) ∧
    ((6 - 6 : ℝ)^2 = 0 ∧ (6 - 5 : ℝ)^2 = 1) := by
  have hg : IsUnit rmseGram.det := by rw [rmse_design_determinant]; norm_num
  refine ⟨rmse_design_gram, ?_, rmse_witness_outcomes.2.2,
    normal_equation_exact_recovery _ _ hg,
    normal_equation_exact_recovery _ _ hg, by norm_num, by norm_num⟩
  intro opposite i
  cases opposite <;> cases hz : i.2.2 <;>
    norm_num [rmseHomogeneousUnit, PotentialUnit.tau, PotentialUnit.receipt,
      PotentialUnit.outcome, bit, hz]

/-- T5(d): positive observation weights preserve exact recovery for the
specified full-column-rank design. This is a general weighted-matrix lemma. -/
theorem rmse_positive_weight_recovery (w : RMSEIndex → ℝ) (hw : ∀ i, 0 < w i)
    (b : Fin 5 → ℝ) :
    let G := rmseQ.transpose * Matrix.diagonal w * rmseQ
    IsUnit G.det ∧ G⁻¹.mulVec (rmseQ.transpose.mulVec
      ((Matrix.diagonal w).mulVec (rmseQ.mulVec b))) = b := by
  have hGram : IsUnit rmseGram.det := by rw [rmse_design_determinant]; norm_num
  have hQ : Function.Injective rmseQ.mulVec := by
    intro x y hxy
    have hx : rmseQ.transpose.mulVec (rmseQ.mulVec x) = rmseGram.mulVec x := by
      rw [Matrix.mulVec_mulVec, rmse_design_gram]
    have hy : rmseQ.transpose.mulVec (rmseQ.mulVec y) = rmseGram.mulVec y := by
      rw [Matrix.mulVec_mulVec, rmse_design_gram]
    have h2 := congrArg rmseQ.transpose.mulVec hxy
    rw [hx,hy] at h2
    have h3 := congrArg rmseGram⁻¹.mulVec h2
    rw [normal_equation_exact_recovery _ _ hGram,
      normal_equation_exact_recovery _ _ hGram] at h3
    exact h3
  have hPD := (Matrix.PosDef.diagonal hw).conjTranspose_mul_mul_same hQ
  have hGT : (rmseQ.transpose * Matrix.diagonal w * rmseQ).PosDef := by
    simpa using hPD
  have hG : IsUnit (rmseQ.transpose * Matrix.diagonal w * rmseQ).det :=
    isUnit_iff_ne_zero.mpr hGT.det_pos.ne'
  refine ⟨hG, ?_⟩
  have heq : rmseQ.transpose.mulVec ((Matrix.diagonal w).mulVec (rmseQ.mulVec b)) =
      (rmseQ.transpose * Matrix.diagonal w * rmseQ).mulVec b := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [heq]
  exact normal_equation_exact_recovery _ _ hG

/-- T9's observed cells (race, assignment, contact).
Rows are Raleigh W contacted / uncontacted-treatment / control, Raleigh
other contacted / uncontacted-treatment / control, then blank-race outside
Raleigh with the same three statuses. Counts total 18,933. -/
def canvassCount (k : Fin 9) : ℕ := ![602,768,2514,160,155,461,1789,5247,7237] k

/-- A complete population with one element per record, including all 18,933
individuals. Compression is used only when summing identical demographic cells. -/
abbrev CanvassRecord : Type := Sigma (fun k : Fin 9 => Fin (canvassCount k))

def canvassRace (i : CanvassRecord) : Option Bool :=
  if i.1.val < 3 then some true else if i.1.val < 6 then some false else none
def canvassZ (i : CanvassRecord) : Bool := decide (i.1.val % 3 < 2)
def canvassContact (i : CanvassRecord) : Bool := decide (i.1.val % 3 = 0)
def raceWorldA (i : CanvassRecord) : Bool := decide (i.1.val < 3)
def raceWorldB (i : CanvassRecord) : Bool := decide (i.1.val < 3 ∨ 6 ≤ i.1.val)
def canvassMass (_ : CanvassRecord) : ℝ := 1/18933

attribute [reducible] canvassContact raceWorldA raceWorldB canvassRace canvassMass

/-- Exact compressed cell masses for T9. A cell with
n_k actual records has mass n_k/18933; the underlying individual population
is still CanvassRecord, rather than a nine-unit population. -/
def canvassCellMass (k : Fin 9) : ℝ := (canvassCount k : ℝ)/18933

/-- T9: summing any cell-constant variable over the 18,933 individual
records equals the count-weighted sum over its nine demographic cells. -/
theorem canvass_cell_expectation (v : Fin 9 → ℝ) :
    fE canvassMass (fun i => v i.1) = fE canvassCellMass v := by
  unfold fE
  rw [Fintype.sum_sigma]
  simp only [canvassMass, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  unfold canvassCellMass
  ring

/-- T9: cell-event probabilities in the actual population equal their
count-weighted cell probabilities; this justifies compressed counting. -/
theorem canvass_cell_probability (A : Fin 9 → Prop) :
    fP canvassMass (fun i => A i.1) = fP canvassCellMass A := by
  classical
  have hleft : fP canvassMass (fun i => A i.1) =
      fE canvassMass (fun i => if A i.1 then (1 : ℝ) else 0) := by
    unfold fP fE
    apply Finset.sum_congr rfl
    intro i _
    by_cases hA : A i.1 <;> simp [hA]
  rw [hleft]
  have hsum := canvass_cell_expectation (fun k => if A k then (1 : ℝ) else 0)
  calc
    _ = fE canvassCellMass (fun k => if A k then (1 : ℝ) else 0) := by
      convert hsum using 1 <;> congr 1 <;> ext i <;> split_ifs <;> rfl
    _ = _ := by
      unfold fE fP
      apply Finset.sum_congr rfl
      intro k _
      by_cases hA : A k <;> simp [hA]

/-- T9: cell-constant conditional means computed on the actual record
population equal those computed with counted cell masses. -/
theorem canvass_cell_conditional_mean (v : Fin 9 → ℝ) (A : Fin 9 → Prop) :
    fCE canvassMass (fun i => v i.1) (fun i => A i.1) =
      fCE canvassCellMass v A := by
  classical
  unfold fCE
  rw [canvass_cell_probability A]
  apply congrArg (fun t : ℝ => t / fP canvassCellMass A)
  have hsum := canvass_cell_expectation (fun k => if A k then v k else 0)
  convert hsum using 1 <;> congr 1 <;> ext i <;> split_ifs <;> rfl

/-- Potential responses in BOTH T9 completions: D₀=0,D₁=recorded contact,
and Y₀=Y₁=the recorded outcome. Every control has C=0. -/
def canvassUnit (Y : CanvassRecord → ℝ) (i : CanvassRecord) : PotentialUnit Unit :=
  ⟨(), false, canvassContact i, Y i, Y i⟩

/-- Compatibility of a full racial classification with every stored label;
None denotes blank race. Raleigh unknown codes are assigned non-white. -/
def preservesRace (W : CanvassRecord → Bool) : Prop :=
  ∀ i b, canvassRace i = some b → W i = b

/-- T9: two complete populations preserve every recorded race, receipt and
outcome but have opposite pooled race/compliance associations. The target's
counts are explicitly realized by 18,933 records. This is non-identification,
not a refutation of the unknown actual population's sign. -/
theorem racial_completion_counterexample (Y : CanvassRecord → ℝ) :
    Fintype.card CanvassRecord = 18933 ∧ ValidLaw canvassMass ∧
    preservesRace raceWorldA ∧ preservesRace raceWorldB ∧
    (∀ i, (canvassUnit Y i).receipt (canvassZ i) = canvassContact i ∧
      (canvassUnit Y i).outcome (canvassZ i) = Y i ∧ ¬ (canvassUnit Y i).defier) ∧
    fP canvassMass (fun i => canvassContact i = true) = 2551/18933 ∧
    fP canvassMass (fun i => raceWorldA i = true) = 3884/18933 ∧
    fP canvassMass (fun i => raceWorldB i = true) = 18157/18933 ∧
    fP canvassMass (fun i => raceWorldA i = true ∧ canvassContact i = true) = 602/18933 ∧
    fP canvassMass (fun i => raceWorldB i = true ∧ canvassContact i = true) = 2391/18933 ∧
    (18933 * 602 - 2551 * 3884 : ℤ) = 1489582 ∧
    (18933 * 2391 - 2551 * 18157 : ℤ) = -1049704 ∧
    fCE canvassMass (fun i => bit (canvassContact i)) (fun i => raceWorldA i = true) -
      fCE canvassMass (fun i => bit (canvassContact i)) (fun i => raceWorldA i = false) =
        744791/29225158 ∧
    fCE canvassMass (fun i => bit (canvassContact i)) (fun i => raceWorldB i = true) -
      fCE canvassMass (fun i => bit (canvassContact i)) (fun i => raceWorldB i = false) =
        -131213/1761229 ∧
    (0 : ℝ) < 744791/29225158 ∧ (-131213/1761229 : ℝ) < 0 := by
  have hcard : Fintype.card CanvassRecord = 18933 := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card (Sigma (fun k : Fin 9 => Fin (canvassCount k))) = 18933
    rw [Nat.card_sigma]
    norm_num [canvassCount, Fin.sum_univ_succ]
  refine ⟨hcard, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro i; norm_num [canvassMass]
    · simp [canvassMass, hcard]
  · rintro ⟨k,j⟩ b
    fin_cases k <;> cases b <;> simp [canvassRace, raceWorldA]
  · rintro ⟨k,j⟩ b
    fin_cases k <;> cases b <;> simp [canvassRace, raceWorldB]
  · rintro ⟨k,j⟩
    fin_cases k <;> simp [canvassUnit, canvassZ, canvassContact,
      PotentialUnit.receipt, PotentialUnit.outcome, PotentialUnit.defier]
  · simp only [canvassContact, raceWorldA, raceWorldB]
    rw [canvass_cell_probability (fun k => decide (k.val % 3 = 0) = true),
      canvass_cell_probability (fun k => decide (k.val < 3) = true),
      canvass_cell_probability (fun k => decide (k.val < 3 ∨ 6 ≤ k.val) = true),
      canvass_cell_probability (fun k => decide (k.val < 3) = true ∧ decide (k.val % 3 = 0) = true),
      canvass_cell_probability (fun k => decide (k.val < 3 ∨ 6 ≤ k.val) = true ∧ decide (k.val % 3 = 0) = true),
      canvass_cell_conditional_mean (fun k => bit (decide (k.val % 3 = 0)))
        (fun k => decide (k.val < 3) = true),
      canvass_cell_conditional_mean (fun k => bit (decide (k.val % 3 = 0)))
        (fun k => decide (k.val < 3) = false),
      canvass_cell_conditional_mean (fun k => bit (decide (k.val % 3 = 0)))
        (fun k => decide (k.val < 3 ∨ 6 ≤ k.val) = true),
      canvass_cell_conditional_mean (fun k => bit (decide (k.val % 3 = 0)))
        (fun k => decide (k.val < 3 ∨ 6 ≤ k.val) = false)]
    norm_num [fP,fCE,fE,canvassCellMass,canvassCount,bit,Fin.sum_univ_succ]

/-- T9: the observed assignment is a supported realization under independent
Bernoulli randomization of these fixed complete populations. Assignment remains
independent of all fixed potential responses and demographics. -/
theorem canvass_assignment_supported (e : ℝ) (he0 : 0 < e) (he1 : e < 1) :
    0 < ∏ i : CanvassRecord, (if canvassZ i then e else 1 - e) := by
  apply Finset.prod_pos
  intro i _
  split <;> linarith

/-- A T9 race completion appends the latent White classification to the
stored race code; it does not overwrite that code. -/
def completedRaceRecord (R : CanvassRecord → Option String)
    (W : CanvassRecord → Bool) (i : CanvassRecord) : Option String × Bool :=
  (R i, W i)

/-- T9: both completions retain every raw recorded race code, and agree
with White/non-White for every nonblank recorded code. Thus the binary
coarsening used for the count calculation loses no code-preservation claim;
in particular every recorded unknown code other than W stays non-White. -/
theorem racial_raw_code_preservation (R : CanvassRecord → Option String)
    (hR : ∀ i code, R i = some code → canvassRace i = some (decide (code = "W"))) :
    (∀ i, (completedRaceRecord R raceWorldA i).1 = R i ∧
      (completedRaceRecord R raceWorldB i).1 = R i) ∧
    (∀ i code, R i = some code →
      raceWorldA i = decide (code = "W") ∧ raceWorldB i = decide (code = "W")) := by
  have hA := (racial_completion_counterexample (fun _ => 0)).2.2.1
  have hB := (racial_completion_counterexample (fun _ => 0)).2.2.2.1
  constructor
  · intro i; exact ⟨rfl,rfl⟩
  · intro i code hi
    exact ⟨hA i _ (hR i code hi),hB i _ (hR i code hi)⟩

/-- Population binary moments expressed through exact counts, T9/T10(a).
These formulas use population denominator N, not an N-1 sample correction. -/
def countCov (N nW nC n11 : ℝ) : ℝ := n11 / N - (nC / N) * (nW / N)
def countComplianceGap (N nW nC n11 : ℝ) : ℝ := n11 / nW - (nC - n11) / (N - nW)
def countRaceGap (N nW nC n11 : ℝ) : ℝ := n11 / nC - (nW - n11) / (N - nC)

/-- T10(a): the same cross-product count determines covariance and both
directions of the conditional binary mean comparison. -/
theorem binary_count_sign_identity (N nW nC n11 : ℝ)
    (hN : 0 < N) (hW : 0 < nW) (hWN : nW < N) (hC : 0 < nC) (hCN : nC < N) :
    countCov N nW nC n11 = (N*n11 - nC*nW) / N^2 ∧
    countComplianceGap N nW nC n11 = (N*n11 - nC*nW) / (nW*(N-nW)) ∧
    countRaceGap N nW nC n11 = (N*n11 - nC*nW) / (nC*(N-nC)) ∧
    (0 < countComplianceGap N nW nC n11 ↔ nC*nW < N*n11) ∧
    (0 < countRaceGap N nW nC n11 ↔ nC*nW < N*n11) := by
  have hNW : 0 < N - nW := by linarith
  have hNC : 0 < N - nC := by linarith
  have hcov : countCov N nW nC n11 = (N*n11 - nC*nW) / N^2 := by
    unfold countCov; field_simp [ne_of_gt hN] <;> ring
  have hcg : countComplianceGap N nW nC n11 = (N*n11 - nC*nW) / (nW*(N-nW)) := by
    unfold countComplianceGap; field_simp [ne_of_gt hW, ne_of_gt hNW] <;> ring
  have hwg : countRaceGap N nW nC n11 = (N*n11 - nC*nW) / (nC*(N-nC)) := by
    unfold countRaceGap; field_simp [ne_of_gt hC, ne_of_gt hNC] <;> ring
  refine ⟨hcov, hcg, hwg, ?_, ?_⟩
  · rw [hcg, div_pos_iff_of_pos_right (mul_pos hW hNW), sub_pos]
  · rw [hwg, div_pos_iff_of_pos_right (mul_pos hC hNC), sub_pos]

/-- T10(b): the recorded Raleigh treatment-arm receipt comparisons are both
negative, with and without unknown race codes. This is a count calculation,
not an assertion about a fitted probit or the unknown pooled racial comparison. -/
theorem raleigh_recorded_comparison :
    (602/1370 - 160/315 : ℝ) = -2957/43155 ∧
    (602/1370 - 155/308 : ℝ) = -13467/210980 ∧
    (602/1370 - 160/315 : ℝ) < 0 ∧ (602/1370 - 155/308 : ℝ) < 0 := by
  norm_num

/-- "n_W = #{W=1}" (and similarly n_C), T9/T10(a).
This is the actual count of a binary variable over a finite population. -/
def binaryCount {n : ℕ} (W : Fin n → Bool) : ℕ :=
  by
  classical
  exact (Finset.univ.filter (fun i => W i = true)).card

/-- "n₁₁ = #{W=1,C=1}", T9/T10(a). -/
def binaryJointCount {n : ℕ} (C W : Fin n → Bool) : ℕ :=
  by
  classical
  exact (Finset.univ.filter (fun i => C i = true ∧ W i = true)).card

attribute [reducible] binaryCount binaryJointCount

/-- T10(a), full finite-population statement: actual binary variables,
their counted margins and their population covariance/conditional means
have the printed count formulas and both conditional comparisons have the
sign of N n₁₁-n_C n_W. All moments use denominator N, not N-1. -/
theorem binary_population_count_sign {n : ℕ} (C W : Fin (n+1) → Bool)
    (hW : 0 < binaryCount W) (hWN : binaryCount W < n+1)
    (hC : 0 < binaryCount C) (hCN : binaryCount C < n+1) :
    let N : ℝ := n+1
    let nW : ℝ := binaryCount W
    let nC : ℝ := binaryCount C
    let n11 : ℝ := binaryJointCount C W
    let p : Fin (n+1) → ℝ := fun _ => 1/N
    fCov p (fun i => bit (C i)) (fun i => bit (W i)) = (N*n11-nC*nW)/N^2 ∧
    fCE p (fun i => bit (C i)) (fun i => W i = true) -
      fCE p (fun i => bit (C i)) (fun i => W i = false) =
        (N*n11-nC*nW)/(nW*(N-nW)) ∧
    fCE p (fun i => bit (W i)) (fun i => C i = true) -
      fCE p (fun i => bit (W i)) (fun i => C i = false) =
        (N*n11-nC*nW)/(nC*(N-nC)) ∧
    (fCE p (fun i => bit (C i)) (fun i => W i = true) >
      fCE p (fun i => bit (C i)) (fun i => W i = false) ↔ nC*nW < N*n11) ∧
    (fCE p (fun i => bit (W i)) (fun i => C i = true) >
      fCE p (fun i => bit (W i)) (fun i => C i = false) ↔ nC*nW < N*n11) := by
  classical
  try dsimp only
  let p : Fin (n+1) → ℝ := fun _ => 1/((n : ℝ)+1)
  have hN : 0 < (n : ℝ)+1 := by positivity
  have hp : (∑ i, p i) = 1 := by simp [p, ne_of_gt hN]
  have hP (A : Fin (n+1) → Prop) :
      fP p A = ((Finset.univ.filter A).card : ℝ)/((n : ℝ)+1) := by
    unfold fP
    calc
      (∑ i, if A i then p i else 0) =
          (1/((n : ℝ)+1)) * (∑ i, if A i then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [p]
        split_ifs <;> ring
      _ = _ := by rw [Finset.sum_boole]; ring
  have hE (A : Fin (n+1) → Bool) :
      fE p (fun i => bit (A i)) = (binaryCount A : ℝ)/((n : ℝ)+1) := by
    have he : fE p (fun i => bit (A i)) = fP p (fun i => A i = true) := by
      unfold fE fP
      apply Finset.sum_congr rfl
      intro i _
      try dsimp only
      by_cases hA : A i = true <;> simp [bit, hA]
    rw [he, hP]
    unfold binaryCount
    congr 3 <;> ext i <;> simp
  have hJ (A B : Fin (n+1) → Bool) :
      fE p (fun i => if B i = true then bit (A i) else 0) =
        (binaryJointCount A B : ℝ)/((n : ℝ)+1) := by
    have he : fE p (fun i => if B i = true then bit (A i) else 0) =
        fP p (fun i => A i = true ∧ B i = true) := by
      unfold fE fP
      apply Finset.sum_congr rfl
      intro i _
      try dsimp only
      by_cases hA : A i = true <;> by_cases hB : B i = true <;> simp [bit, hA, hB]
    rw [he, hP]
    unfold binaryJointCount
    congr 3 <;> ext i <;> simp
  have hF (B : Fin (n+1) → Bool) :
      fP p (fun i => B i = false) = 1-(binaryCount B : ℝ)/((n : ℝ)+1) := by
    have hsum : fP p (fun i => B i = false) =
        (∑ i, p i) - fP p (fun i => B i = true) := by
      unfold fP
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hB : B i = true
      · simp [hB]
      · have hf : B i = false := Bool.eq_false_of_not_eq_true hB
        simp [hB,hf]
    rw [hsum,hp,hP]
    unfold binaryCount
    congr 4 <;> ext i <;> simp
  have hJF (A B : Fin (n+1) → Bool) :
      fE p (fun i => if B i = false then bit (A i) else 0) =
        ((binaryCount A : ℝ)-(binaryJointCount A B : ℝ))/((n : ℝ)+1) := by
    have hi (i : Fin (n+1)) :
        p i*(if B i = false then bit (A i) else 0) =
        p i*bit (A i)-p i*(if B i = true then bit (A i) else 0) := by
      cases hB : B i <;> simp [hB]
    unfold fE
    simp_rw [hi]
    rw [Finset.sum_sub_distrib]
    change fE p (fun i => bit (A i)) -
      fE p (fun i => if B i = true then bit (A i) else 0) = _
    rw [hE, hJ, sub_div]
  have hJT : binaryJointCount W C = binaryJointCount C W := by
    unfold binaryJointCount
    simp_rw [and_comm]
  have hprod : fE p (fun i => bit (C i)*bit (W i)) =
      (binaryJointCount C W : ℝ)/((n : ℝ)+1) := by
    have hi (i : Fin (n+1)) : bit (C i)*bit (W i) =
        if W i = true then bit (C i) else 0 := by cases W i <;> simp [bit]
    simp_rw [hi]
    exact hJ C W
  have hcT (A B : Fin (n+1) → Bool) :
      fCE p (fun i => bit (A i)) (fun i => B i = true) =
        (binaryJointCount A B : ℝ)/(binaryCount B : ℝ) := by
    unfold fCE
    try dsimp only
    calc
      _ = ((binaryJointCount A B : ℝ)/((n : ℝ)+1)) /
          ((binaryCount B : ℝ)/((n : ℝ)+1)) := by
        congr 1
        · convert hJ A B using 1 <;> congr 1 <;> ext i <;> split_ifs <;> rfl
        · convert hP (fun i => B i = true) using 1 <;>
            unfold binaryCount <;> congr 3 <;> ext i <;> simp
      _ = _ := div_div_div_cancel_right₀ (ne_of_gt hN) _ _
  have hcF (A B : Fin (n+1) → Bool) :
      fCE p (fun i => bit (A i)) (fun i => B i = false) =
        ((binaryCount A : ℝ)-(binaryJointCount A B : ℝ)) /
          (((n : ℝ)+1)-(binaryCount B : ℝ)) := by
    unfold fCE
    try dsimp only
    have hden : 1-(binaryCount B : ℝ)/((n : ℝ)+1) =
        (((n : ℝ)+1)-(binaryCount B : ℝ))/((n : ℝ)+1) := by
      field_simp [ne_of_gt hN]
    calc
      _ = (((binaryCount A : ℝ)-(binaryJointCount A B : ℝ))/((n : ℝ)+1)) /
          (1-(binaryCount B : ℝ)/((n : ℝ)+1)) := by
        congr 1
        · convert hJF A B using 1 <;> congr 1 <;> ext i <;> split_ifs <;> rfl
        · exact hF B
      _ = _ := by rw [hden]; exact div_div_div_cancel_right₀ (ne_of_gt hN) _ _
  have hw : (0 : ℝ) < binaryCount W := by exact_mod_cast hW
  have hwN : (binaryCount W : ℝ) < (n : ℝ)+1 := by exact_mod_cast hWN
  have hc : (0 : ℝ) < binaryCount C := by exact_mod_cast hC
  have hcN : (binaryCount C : ℝ) < (n : ℝ)+1 := by exact_mod_cast hCN
  have hid := binary_count_sign_identity ((n : ℝ)+1) (binaryCount W)
    (binaryCount C) (binaryJointCount C W) hN hw hwN hc hcN
  change fCov p (fun i => bit (C i)) (fun i => bit (W i)) = _ ∧ _
  simp only [fCov, hprod, hE]
  rw [hcT C W, hcF C W, hcT W C, hcF W C, hJT]
  simpa only [countCov, countComplianceGap, countRaceGap, sub_pos] using hid

/-- Group means for a finite law, used in T10(d)'s within/between-city
covariance decomposition. -/
def fGroupMean {L G : Type*} [Fintype L] (p s : L → ℝ) (group : L → G) (g : G) : ℝ :=
  fCE p s (fun i => group i = g)


/-- T11(A): complier probability 3/4, defier probability 1/4. -/
def semTypeMass (t : Bool) : ℝ := if t then 1/4 else 3/4
def semDefierUnit (t : Bool) : PotentialUnit Unit :=
  ⟨(), t, !t, bit t - 1/4, bit t - 1/4 + 1⟩
def semDefierMass : Bool × Bool → ℝ := randomized semTypeMass (1/4)
def semDefierError (i : Bool × Bool) : ℝ :=
  bit ((semDefierUnit i.1).receipt i.2) - 1/4 - bit i.2 / 2

/-- T11(A): a constant-effect SEM with a valid, endogenous first stage,
zero instrument/error correlation and randomized assignment nevertheless has
defiers with probability 1/4. It refutes the p. 495 nesting claim. -/
theorem sem_defier_counterexample :
    ValidLaw semDefierMass ∧
    FIndep semDefierMass
      (fun i => ((semDefierUnit i.1).x, (semDefierUnit i.1).d0, (semDefierUnit i.1).d1,
        (semDefierUnit i.1).y0, (semDefierUnit i.1).y1)) Prod.snd ∧
    (∀ i : Bool × Bool, (semDefierUnit i.1).tau = 1 ∧
      (semDefierUnit i.1).outcome i.2 = bit ((semDefierUnit i.1).receipt i.2) +
        (semDefierUnit i.1).y0 ∧
      bit ((semDefierUnit i.1).receipt i.2) = 1/4 + bit i.2/2 + semDefierError i) ∧
    (∀ z, fCE semDefierMass semDefierError (fun i => i.2 = z) = 0) ∧
    fE semDefierMass (fun i => bit i.2) = 1/4 ∧
    fVar semDefierMass (fun i => bit i.2) = 3/16 ∧
    fE semDefierMass (fun i => (semDefierUnit i.1).y0) = 0 ∧
    fVar semDefierMass (fun i => (semDefierUnit i.1).y0) = 3/16 ∧
    fCov semDefierMass (fun i => bit i.2) (fun i => (semDefierUnit i.1).y0) = 0 ∧
    fCorr semDefierMass (fun i => bit i.2) (fun i => (semDefierUnit i.1).y0) = 0 ∧
    fCov semDefierMass (fun i => bit i.2)
      (fun i => bit ((semDefierUnit i.1).receipt i.2)) = 3/32 ∧
    fCov semDefierMass (fun i => bit ((semDefierUnit i.1).receipt i.2))
      (fun i => (semDefierUnit i.1).y0) = 3/32 ∧
    fP semDefierMass (fun i => (semDefierUnit i.1).defier) = 1/4 := by
  have ht : ValidLaw semTypeMass := by
    constructor
    · intro t; cases t <;> norm_num [semTypeMass]
    · norm_num [semTypeMass, Fintype.sum_bool]
  have hv := randomized_valid semTypeMass (1/4) ht (by norm_num) (by norm_num)
  have hi := randomized_independent semTypeMass (1/4) ht
    (fun t => ((semDefierUnit t).x, (semDefierUnit t).d0, (semDefierUnit t).d1,
      (semDefierUnit t).y0, (semDefierUnit t).y1))
  refine ⟨hv, hi, ?_, ?_, ?_⟩
  · rintro ⟨t,z⟩; cases t <;> cases z <;>
      norm_num [semDefierUnit, semDefierError, bit, PotentialUnit.tau,
        PotentialUnit.outcome, PotentialUnit.receipt]
  · intro z; cases z <;> norm_num [fCE, fP, fE, semDefierError, semDefierUnit,
      semDefierMass, randomized, semTypeMass, bit, PotentialUnit.receipt,
      Fintype.sum_prod_type, Fintype.sum_bool]
  · norm_num [fCorr, fVar, fCov, fE, fP, semDefierUnit, semDefierMass,
      randomized, semTypeMass, bit, PotentialUnit.receipt, PotentialUnit.defier,
      Fintype.sum_prod_type, Fintype.sum_bool]

/-- T11(B): U uniform on {-2,-1,1,2}, Z=1{|U|=2}, D₀=1{U>0}, D₁=1.
The SEM's zero moment correlation does not make Z independent of outcomes. -/
def dependentUnit (i : Fin 4) : PotentialUnit Unit :=
  let u : ℝ := ![-2,-1,1,2] i
  ⟨(), decide (0 < u), true, u, u + 1⟩
def dependentZ (i : Fin 4) : Bool := decide (i.val = 0 ∨ i.val = 3)
def dependentError (i : Fin 4) : ℝ :=
  bit ((dependentUnit i).receipt (dependentZ i)) - 1/2 - bit (dependentZ i)/2

/-- T11(B): the SEM equations and exogeneity/relevance moments hold, but
Z is not independent of Y₀, even though no defiers exist and E(u|Z)=0. -/
theorem sem_dependence_counterexample :
    ValidLaw (fun _ : Fin 4 => (1/4 : ℝ)) ∧
    (∀ i, (dependentUnit i).tau = 1 ∧ (dependentUnit i).outcome (dependentZ i) =
      bit ((dependentUnit i).receipt (dependentZ i)) + (dependentUnit i).y0 ∧
      bit ((dependentUnit i).receipt (dependentZ i)) = 1/2 + bit (dependentZ i)/2 + dependentError i) ∧
    (∀ z, fCE (fun _ => 1/4) dependentError (fun i => dependentZ i = z) = 0 ∧
      fCE (fun _ => 1/4) (fun i => (dependentUnit i).y0) (fun i => dependentZ i = z) = 0) ∧
    fVar (fun _ => 1/4) (fun i => bit (dependentZ i)) = 1/4 ∧
    fVar (fun _ => 1/4) (fun i => (dependentUnit i).y0) = 5/2 ∧
    fCorr (fun _ => 1/4) (fun i => bit (dependentZ i)) (fun i => (dependentUnit i).y0) = 0 ∧
    fCov (fun _ => 1/4) (fun i => bit (dependentZ i))
      (fun i => bit ((dependentUnit i).receipt (dependentZ i))) = 1/8 ∧
    fCov (fun _ => 1/4) (fun i => bit ((dependentUnit i).receipt (dependentZ i)))
      (fun i => (dependentUnit i).y0) = 1/4 ∧
    fP (fun _ => 1/4) (fun i => (dependentUnit i).defier) = 0 ∧
    ¬ FIndep (fun _ => 1/4) (fun i => (dependentUnit i).y0) dependentZ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro i; norm_num
    · norm_num [Fin.sum_univ_succ]
  · intro i; fin_cases i <;> norm_num [dependentUnit, dependentZ, dependentError,
      bit, PotentialUnit.tau, PotentialUnit.outcome, PotentialUnit.receipt]
  · intro z; cases z <;> norm_num [fCE, fP, fE, dependentUnit, dependentZ,
      dependentError, bit, PotentialUnit.receipt, Fin.sum_univ_succ]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try norm_num [fCorr, fVar, fCov, fE, fP, dependentUnit, dependentZ,
      bit, PotentialUnit.receipt, PotentialUnit.defier, Fin.sum_univ_succ]
    intro h
    have hh := h (2 : ℝ) true
    norm_num [fP, dependentUnit, dependentZ, Fin.sum_univ_succ] at hh

/-- T12(b): the paper's causal reading of SEM equation (1), pp. 493-494,
forces Y₁ᵢ-Y₀ᵢ=β₁. Covariates and u are held fixed under both interventions. -/
theorem sem_forces_constant_effect {I K : Type*} [Fintype K]
    (Y0 Y1 u : I → ℝ) (Q : I → K → ℝ) (β0 β1 : ℝ) (coeff : K → ℝ)
    (h0 : ∀ i, Y0 i = β0 + (∑ k, coeff k * Q i k) + u i)
    (h1 : ∀ i, Y1 i = β0 + β1 + (∑ k, coeff k * Q i k) + u i) :
    ∀ i, Y1 i - Y0 i = β1 := by
  intro i; rw [h0 i, h1 i]; ring

/-- T12(C): every unit is a complier, while H is 1 or 2 with equal probability. -/
def heterogeneousUnit (h : Bool) : PotentialUnit Unit :=
  ⟨(), false, true, 0, if h then 2 else 1⟩

/-- T12(c): all five IV assumptions allow heterogeneous effects. Together
with T11 and the SEM subtraction lemma this proves the two assumption sets
are not nested. The ATE, LATE and observed Wald ratio here are 3/2. -/
theorem heterogeneous_iv_counterexample :
    FIV (randomized (fun _ : Bool => 1/2) (1/2)) (liftUnit heterogeneousUnit) Prod.snd ∧
    (heterogeneousUnit false).tau = 1 ∧ (heterogeneousUnit true).tau = 2 ∧
    ¬ (∃ β : ℝ, ∀ h, (heterogeneousUnit h).tau = β) ∧
    fE (randomized (fun _ : Bool => 1/2) (1/2)) (fun i => (heterogeneousUnit i.1).tau) = 3/2 ∧
    fWald (randomized (fun _ : Bool => 1/2) (1/2)) (liftUnit heterogeneousUnit) Prod.snd
      (fun _ => 1) = 3/2 := by
  have ht : ValidLaw (fun _ : Bool => (1/2 : ℝ)) := by
    constructor
    · intro b; norm_num
    · norm_num [Fintype.sum_bool]
  have hv := randomized_valid (fun _ : Bool => (1/2 : ℝ)) (1/2) ht (by norm_num) (by norm_num)
  have hi := randomized_independent (fun _ : Bool => (1/2 : ℝ)) (1/2) ht
    (fun h => ((heterogeneousUnit h).x, (heterogeneousUnit h).d0, (heterogeneousUnit h).d1,
      (heterogeneousUnit h).y0, (heterogeneousUnit h).y1))
  refine ⟨⟨hv, ?_, ?_, hi, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals try norm_num [fCE, fP, fE, fWald, liftUnit, randomized, heterogeneousUnit,
    bit, PotentialUnit.receipt, PotentialUnit.outcome, PotentialUnit.defier,
    PotentialUnit.tau, Fintype.sum_prod_type, Fintype.sum_bool]

/-- Closed saturated likelihood for a stratum, equation (7), pp. 496-497,
with q≤p and boundary fits included (T13/T14). -/
def saturatedLikelihood (n1 n0 k1 k0 : ℕ) (p q : ℝ) : ℝ :=
  p^k1 * (1-p)^(n1-k1) * q^k0 * (1-q)^(n0-k0)

def receiptTriangle : Set (ℝ × ℝ) := {v | 0 ≤ v.2 ∧ v.2 ≤ v.1 ∧ v.1 ≤ 1}

/-- Corrected saturated ML fit, T14(a): separate empirical arm rates if
ordered; otherwise both arms are pooled. Its ML status is proved separately. -/
def saturatedFit (n1 n0 k1 k0 : ℕ) : ℝ × ℝ :=
  if (k0 : ℝ) / n0 ≤ (k1 : ℝ) / n1 then ((k1 : ℝ) / n1, (k0 : ℝ) / n0)
  else (((k1 + k0 : ℕ) : ℝ) / (n1 + n0), ((k1 + k0 : ℕ) : ℝ) / (n1 + n0))

/-- T14's fitted score max(r₁-r₀,0), before clipping or Winsorization. -/
def positiveScore (r1 r0 : ℝ) : ℝ := max (r1 - r0) 0


/-- T13's two-observation extended ML fit, one independent receipt per arm. -/
def twoObservationFit (d : Bool × Bool) : ℝ × ℝ :=
  if d.1 then (if d.2 then (1,1) else (1,0))
  else (if d.2 then (1/2,1/2) else (0,0))
def twoObservationLaw (d : Bool × Bool) : ℝ :=
  (if d.1 then 3/4 else 1/4) * (if d.2 then 1/4 else 3/4)
def twoObservationLikelihood (d : Bool × Bool) (p q : ℝ) : ℝ :=
  bernoulliFactor p d.1 * bernoulliFactor q d.2

/-- T13(i): all four actual likelihood maxima have exact global polynomial
certificates on the triangle. This links the bias calculation to ML. -/
theorem two_observation_ml_maxima (d : Bool × Bool) :
    twoObservationFit d ∈ receiptTriangle ∧
    ∀ v ∈ receiptTriangle, twoObservationLikelihood d v.1 v.2 ≤
      twoObservationLikelihood d (twoObservationFit d).1 (twoObservationFit d).2 := by
  rcases d with ⟨d1,d0⟩
  constructor
  · cases d1 <;> cases d0 <;> norm_num [twoObservationFit, receiptTriangle]
  · rintro ⟨p,q⟩ ⟨hq0,hqp,hp1⟩
    have hp0 : 0 ≤ p := le_trans hq0 hqp
    have hq1 : q ≤ 1 := le_trans hqp hp1
    have ha := mul_nonneg (sub_nonneg.mpr hp1) hq0
    have hb := mul_nonneg hp0 hq0
    have hc := mul_nonneg hp0 (sub_nonneg.mpr hq1)
    have hd := mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hqp)
    cases d1 <;> cases d0 <;>
      norm_num [twoObservationLikelihood, bernoulliFactor, twoObservationFit] <;>
      nlinarith [sq_nonneg (p - 1/2)]

/-- T13(ii)-(iii): the genuine closed ML score is 1 only for receipts (1,0),
so its expectation is 9/16, not the true compliance 1/2. The raw difference
is unbiased. The data law is normalized and uses independent arms. -/
theorem saturated_unbiasedness_counterexample :
    ValidLaw twoObservationLaw ∧
    (∀ d, (twoObservationFit d).1 - (twoObservationFit d).2 =
      if d.1 = true ∧ d.2 = false then 1 else 0) ∧
    fE twoObservationLaw (fun d => (twoObservationFit d).1 - (twoObservationFit d).2) = 9/16 ∧
    fE twoObservationLaw (fun d => bit d.1 - bit d.2) = 1/2 ∧
    (9/16 : ℝ) - 1/2 = 1/16 ∧ (9/16 : ℝ) ≠ 1/2 ∧
    nestedReceipt (3/4) (1/3) true = 3/4 ∧ nestedReceipt (3/4) (1/3) false = 1/4 := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨d1,d0⟩; cases d1 <;> cases d0 <;> norm_num [twoObservationLaw]
    · norm_num [twoObservationLaw, Fintype.sum_prod_type, Fintype.sum_bool]
  · rintro ⟨d1,d0⟩; cases d1 <;> cases d0 <;> norm_num [twoObservationFit]
  · norm_num [fE, twoObservationLaw, twoObservationFit, nestedReceipt, bit,
      Fintype.sum_prod_type, Fintype.sum_bool]

/-- Binomial count distribution, T13(iv)/T14(b)-(d): the finite probability
of k successes in n independent Bernoulli(p) draws. -/
def binomialMass (n : ℕ) (p : ℝ) (k : Fin (n+1)) : ℝ :=
  (n.choose k.val : ℝ) * p^k.val * (1-p)^(n-k.val)
def binomialArmLaw (n1 n0 : ℕ) (p1 p0 : ℝ) : Fin (n1+1) × Fin (n0+1) → ℝ :=
  fun k => binomialMass n1 p1 k.1 * binomialMass n0 p0 k.2
def armRateScore (n1 n0 : ℕ) (k : Fin (n1+1) × Fin (n0+1)) : ℝ :=
  positiveScore ((k.1.val : ℝ)/n1) ((k.2.val : ℝ)/n0)

/-- T13(iv): exact enumeration with five units per arm gives the reported
larger-sample bias and inverted-rate probability, not just a one-unit anomaly. -/
theorem five_per_arm_bias_counterexample :
    fE (binomialArmLaw 5 5 (1/2) (3/10)) (armRateScore 5 5) = 15659/64000 ∧
    (15659/64000 : ℝ) - 1/5 = 2859/64000 ∧
    fP (binomialArmLaw 5 5 (1/2) (3/10)) (fun k => k.1.val < k.2.val) = 257079/1600000 := by
  norm_num [fE, fP, binomialArmLaw, binomialMass, armRateScore, positiveScore,
    Fintype.sum_prod_type, Fin.sum_univ_succ, Nat.choose]

/-- T14(c), finite contraction lemma: truncating an empirical difference
at zero cannot increase its error about a nonnegative true compliance score. -/
theorem positive_part_error_bound (t c : ℝ) (hc : 0 ≤ c) :
    |max t 0 - c| ≤ |t - c| := by
  by_cases ht : 0 ≤ t
  · simp [max_eq_left ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [max_eq_right ht', zero_sub, abs_neg, abs_of_nonneg hc,
      abs_of_nonpos (by linarith : t - c ≤ 0)]
    linarith

/-- T14(b), finite bias identity: E(max(T,0))-E(T)=E(max(-T,0))≥0.
This exact identity is independent of the likelihood maximization proof. -/
theorem positive_part_bias_identity {L : Type*} [Fintype L] (p T : L → ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    fE p (fun i => max (T i) 0) - fE p T = fE p (fun i => max (-T i) 0) ∧
    0 ≤ fE p (fun i => max (-T i) 0) := by
  constructor
  · unfold fE
    try dsimp only
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    try dsimp only
    by_cases h : 0 ≤ T i
    · rw [max_eq_left h, max_eq_right (by linarith : -T i ≤ 0)]; ring
    · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith : 0 ≤ -T i)]; ring
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hp i) (le_max_right _ _)


/-- Successor order-statistic index, capped at the last observation. -/
def nextOrderIndex {n : ℕ} (j : Fin (n+1)) : Fin (n+1) :=
  ⟨min (j.val+1) n, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- R type-7 interpolated sample quantile, T16(i), footnote 6 p. 498 and the
application scripts: h=1+(N-1)λ, j=floor h, γ=h-j. The Fin index is j-1,
and a sorting permutation preserves every observation including ties.
The relational form avoids selecting an arbitrary quantile implementation. -/
def Type7Quantile {n : ℕ} (s : Fin (n+1) → ℝ) (level c : ℝ) : Prop :=
  ∃ π : Equiv.Perm (Fin (n+1)), Monotone (fun i => s (π i)) ∧
    ∃ j : Fin (n+1), (j.val : ℝ) ≤ (n : ℝ)*level ∧ (n : ℝ)*level < (j.val : ℝ)+1 ∧
      c = (1 - ((n : ℝ)*level - j.val)) * s (π j) +
        ((n : ℝ)*level - j.val) * s (π (nextOrderIndex j))

/-- Strictly-below-cutoff count, footnote 6: only these scores are replaced. -/
def belowCount {n : ℕ} (s : Fin (n+1) → ℝ) (c : ℝ) : ℕ :=
  (Finset.univ.filter (fun i => s i < c)).card

/-- T15(ii): every interpolated quantile of a constant sample is that
constant, for every positive sample size. The defining hypotheses are inhabited. -/
theorem constant_quantile {n : ℕ} (a level : ℝ) (hlevel : level ∈ Icc (0 : ℝ) 1) :
    Type7Quantile (fun _ : Fin (n+1) => a) level a ∧
    (∀ c, Type7Quantile (fun _ : Fin (n+1) => a) level c → c = a) := by
  have hnonneg : 0 ≤ (n : ℝ)*level := mul_nonneg (Nat.cast_nonneg n) hlevel.1
  have hupper : (n : ℝ)*level < ((n+1 : ℕ) : ℝ) := by
    have hle := mul_le_mul_of_nonneg_left hlevel.2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    norm_num at hle ⊢
    linarith
  let j : Fin (n+1) := ⟨Nat.floor ((n : ℝ)*level), (Nat.floor_lt hnonneg).2 hupper⟩
  constructor
  · refine ⟨Equiv.refl _, ?_, j, Nat.floor_le hnonneg, Nat.lt_floor_add_one _, ?_⟩
    · intro i k _; simp
    · ring
  · rintro c ⟨π,hπ,j,hj,hj1,hc⟩
    rw [hc]
    ring

/-- T15(ii): the score quantile c_n=1/2 does not tend to zero. This refutes
the footnote's stated rationale while leaving consistency untouched. -/
theorem cutoff_not_zero :
    ¬ Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 0) ∧
    (∀ n (level : ℝ), level ∈ Icc (0 : ℝ) 1 →
      Type7Quantile (fun _ : Fin (n+1) => (1/2 : ℝ)) level (1/2)) ∧
    (∀ n, belowCount (fun _ : Fin (n+1) => (1/2 : ℝ)) (1/2) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hh : (1/2 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds h
    norm_num at hh
  · intro n level hlevel
    exact (constant_quantile (n := n) (1/2) level hlevel).1
  · intro n; simp [belowCount]

/-- T15(i),(iii): the law used for the nonzero cutoff satisfies the five IV
assumptions, Assumption 1 and overlap; the true-score ratio equals its ATE 1.
Oracle scores equal to the true constant score have zero estimation error. -/
theorem constant_score_counterexample_law :
    FIV sixMass (liftUnit constantUnit) Prod.snd ∧
    fLatentIgnorability sixMass (liftUnit constantUnit) ∧
    fScore sixMass (liftUnit constantUnit) () = 1/2 ∧
    (1/4 : ℝ) < fScore sixMass (liftUnit constantUnit) () ∧
    fE sixMass (fun i => (constantUnit i.1).tau) = 1 ∧
    fWald sixMass (liftUnit constantUnit) Prod.snd (fun _ => 2) = 1 := by
  have ht : ValidLaw typeMass := by
    constructor
    · intro i; unfold typeMass; split <;> norm_num
    · norm_num [typeMass, Fin.sum_univ_succ]
  have hv := randomized_valid typeMass (1/2) ht (by norm_num) (by norm_num)
  have hi := randomized_independent typeMass (1/2) ht
    (fun i => ((constantUnit i).x, (constantUnit i).d0, (constantUnit i).d1,
      (constantUnit i).y0, (constantUnit i).y1))
  refine ⟨⟨hv, ?_, ?_, hi, ?_, ?_⟩, ?_, ?_⟩
  all_goals try norm_num [fCE, fP, fE, fScore, fWald, sixMass, liftUnit,
    randomized, typeMass, constantUnit, bit, PotentialUnit.receipt,
    PotentialUnit.outcome, PotentialUnit.complier, PotentialUnit.defier,
    PotentialUnit.tau, Fintype.sum_prod_type, Fin.sum_univ_succ]
  rintro ⟨⟩ _
  norm_num [fCE, fP, fE, sixMass, liftUnit, randomized, typeMass, constantUnit,
    PotentialUnit.complier, PotentialUnit.tau, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- T16(i)-(ii): the changed fraction is bounded by λ+1/N and a score
lower bound also bounds the cutoff. This states the actual sorting/interpolation
rule including ties, rather than assuming its desired count bound. -/
theorem quantile_count_and_lower_bound {n : ℕ} (s : Fin (n+1) → ℝ) (level c b : ℝ)
    (hlevel : level ∈ Ioo (0 : ℝ) 1) (hq : Type7Quantile s level c) (hb : ∀ i, b ≤ s i) :
    (belowCount s c : ℝ) ≤ 1 + n*level ∧
    (belowCount s c : ℝ)/(n+1) ≤ level + 1/(n+1) ∧ b ≤ c := by
  rcases hq with ⟨π, hπ, j, hj, hj1, hc⟩
  let γ : ℝ := n*level-j.val
  have hγ0 : 0 ≤ γ := by dsimp [γ]; linarith
  have hγ1 : γ ≤ 1 := by dsimp [γ]; linarith
  have hnj : j ≤ nextOrderIndex j := by
    change j.val ≤ min (j.val+1) n
    omega
  have hsorted := hπ hnj
  have hcut : c ≤ s (π (nextOrderIndex j)) := by
    have hh := mul_nonneg (sub_nonneg.mpr hγ1) (sub_nonneg.mpr hsorted)
    change c = (1-γ)*s (π j)+γ*s (π (nextOrderIndex j)) at hc
    nlinarith
  have hlower : b ≤ c := by
    have h0 := mul_nonneg (sub_nonneg.mpr hγ1) (sub_nonneg.mpr (hb (π j)))
    have h1 := mul_nonneg hγ0 (sub_nonneg.mpr (hb (π (nextOrderIndex j))))
    change c = (1-γ)*s (π j)+γ*s (π (nextOrderIndex j)) at hc
    nlinarith
  have hmaps : Set.MapsTo π.symm
      (↑(Finset.univ.filter (fun i => s i < c)) : Set (Fin (n+1)))
      (↑(Finset.Iio (nextOrderIndex j)) : Set (Fin (n+1))) := by
    intro i hi
    have hsi : s i < c := (Finset.mem_filter.mp hi).2
    apply Finset.mem_Iio.mpr
    by_contra hnot
    have hh := hπ (le_of_not_gt hnot)
    simp only [Equiv.apply_symm_apply] at hh
    linarith
  have hcard : belowCount s c ≤ (nextOrderIndex j).val := by
    simpa [belowCount] using Finset.card_le_card_of_injOn π.symm hmaps π.symm.injective.injOn
  have hnext : (nextOrderIndex j).val ≤ j.val+1 := min_le_left _ _
  have hcountj : (belowCount s c : ℝ) ≤ j.val+1 := by
    exact_mod_cast hcard.trans hnext
  have hcount : (belowCount s c : ℝ) ≤ 1+n*level := by linarith
  refine ⟨hcount, ?_, hlower⟩
  have hn : (0 : ℝ) < n+1 := by positivity
  apply (div_le_iff₀ hn).2
  have hright : (level+1/(n+1))*(n+1) = (n+1)*level+1 := by field_simp <;> ring
  rw [hright]
  nlinarith [hlevel.1]

/-- T16(i), asymptotic changed-fraction statement for the exact quantile rule:
at N^(-alpha), alpha>0, the fraction strictly below the cutoff tends to zero
for every sequence of samples, irrespective of their score distribution. -/
theorem quantile_changed_fraction_tends_zero (s : (n : ℕ) → Fin (n+1) → ℝ)
    (c : ℕ → ℝ) (α : ℝ) (hα : 0 < α)
    (hq : ∀ n, Type7Quantile (s n) (((n+1 : ℕ) : ℝ)^(-α)) (c n)) :
    Tendsto (fun n => (belowCount (s n) (c n) : ℝ)/(n+1)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hpow := (tendsto_rpow_neg_atTop hα).comp hcast
  have hinv := tendsto_inv_atTop_zero.comp hcast
  have hbound : Tendsto (fun n : ℕ => (((n+1 : ℕ) : ℝ)^(-α))+1/(n+1))
      atTop (𝓝 0) := by
    simpa [one_div] using hpow.add hinv
  refine squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ hbound
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hn1 : (1 : ℝ) < ((n+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n+1)
  have hlevel : (((n+1 : ℕ) : ℝ)^(-α)) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.rpow_pos_of_pos hn0 _, Real.rpow_lt_one_of_one_lt_of_neg hn1 (neg_lt_zero.mpr hα)⟩
  let b : ℝ := (Finset.univ : Finset (Fin (n+1))).inf' Finset.univ_nonempty (s n)
  have hb : ∀ i, b ≤ s n i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  exact (quantile_count_and_lower_bound (s n) _ (c n) b hlevel (hq n) hb).2.1

/-- Weight change after Winsorization, footnote 6 p. 498. -/
def weightChange (s c : ℝ) : ℝ := 1/s - 1/max s c

/-- T16(iii), pointwise finite core: the weight change is nonnegative and
bounded by b⁻¹ times the indicator of a score strictly below the cutoff. -/
theorem weight_change_bound (s c b : ℝ) (hb : 0 < b) (hs : b ≤ s) :
    0 ≤ weightChange s c ∧ weightChange s c ≤ (1/b) * (if s < c then 1 else 0) := by
  have hs0 : 0 < s := lt_of_lt_of_le hb hs
  have hc0 : 0 < max s c := lt_of_lt_of_le hs0 (le_max_left _ _)
  constructor
  · exact sub_nonneg.mpr (one_div_le_one_div_of_le hs0 (le_max_left _ _))
  · by_cases hsc : s < c
    · rw [weightChange, max_eq_right hsc.le, if_pos hsc, mul_one]
      have hcb : 0 < c := lt_trans hs0 hsc
      have hsb := one_div_le_one_div_of_le hb hs
      have hc := one_div_pos.mpr hcb
      linarith
    · simp [weightChange, max_eq_left (le_of_not_gt hsc), hsc]

/-- T16(iii): the change in a bounded weighted mean is controlled by the
number of changed scores. Together with the quantile count theorem this
gives K/b*(λ+1/N). No bound on unbounded outcomes is silently assumed. -/
theorem bounded_weighted_mean_change {n : ℕ} (s V : Fin (n+1) → ℝ)
    (c b K : ℝ) (hb : 0 < b) (hs : ∀ i, b ≤ s i) (hK : 0 ≤ K)
    (hV : ∀ i, |V i| ≤ K) :
    |(∑ i, weightChange (s i) c * V i)/(n+1)| ≤
      (K/b) * ((belowCount s c : ℝ)/(n+1)) := by
  have hn : (0 : ℝ) < n+1 := by positivity
  have hpoint : ∀ i, |weightChange (s i) c * V i| ≤
      (K/b)*(if s i < c then 1 else 0) := by
    intro i
    have hw := weight_change_bound (s i) c b hb (hs i)
    by_cases hsc : s i < c
    · rw [abs_mul, abs_of_nonneg hw.1, if_pos hsc, mul_one]
      have hwb : weightChange (s i) c ≤ 1/b := by simpa [hsc] using hw.2
      calc
        weightChange (s i) c * |V i| ≤ (1/b)*K :=
          mul_le_mul hwb (hV i) (abs_nonneg _) (one_div_pos.mpr hb).le
        _ = K/b := by ring
    · simp [weightChange, max_eq_left (le_of_not_gt hsc), hsc]
  have hsum : |∑ i, weightChange (s i) c * V i| ≤ (K/b)*(belowCount s c : ℝ) := by
    calc
      |∑ i, weightChange (s i) c * V i| ≤ ∑ i, |weightChange (s i) c * V i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (K/b)*(if s i < c then 1 else 0) :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = (K/b)*(belowCount s c : ℝ) := by
        rw [← Finset.mul_sum]
        simp [belowCount]
  rw [abs_div, abs_of_pos hn]
  calc
    |∑ i, weightChange (s i) c * V i|/(n+1) ≤
        ((K/b)*(belowCount s c : ℝ))/(n+1) :=
      div_le_div_of_nonneg_right hsum hn.le
    _ = (K/b)*((belowCount s c : ℝ)/(n+1)) := by ring

/-- T16 finite core: uniform score accuracy bounds the inverse-score error
and ensures every estimated score exceeds ε/2. -/
theorem inverse_score_accuracy (p s ε r : ℝ) (he : 0 < ε) (hp : ε < p)
    (hr0 : 0 ≤ r) (hr : r < ε/2) (herr : |s-p| ≤ r) :
    ε/2 < s ∧ |1/s - 1/p| ≤ 2*r/ε^2 := by
  have hlow := (abs_le.mp herr).1
  have hs : ε/2 < s := by linarith
  have hs0 : 0 < s := by linarith
  have hp0 : 0 < p := lt_trans he hp
  have hsp0 : 0 < s*p := mul_pos hs0 hp0
  have hep : 0 < ε^2/2 := by positivity
  have hprod : ε^2/2 ≤ s*p := by
    have h := mul_le_mul hs.le hp.le he.le hs0.le
    nlinarith
  refine ⟨hs, ?_⟩
  calc
    |1/s - 1/p| = |s-p|/(s*p) := by
      rw [div_sub_div _ _ hs0.ne' hp0.ne', one_mul, mul_one,
        abs_div, abs_mul, abs_of_pos hs0, abs_of_pos hp0, abs_sub_comm]
    _ ≤ r/(s*p) := div_le_div_of_nonneg_right herr hsp0.le
    _ ≤ r/(ε^2/2) := div_le_div_of_nonneg_left hr0 hep hprod
    _ = 2*r/ε^2 := by field_simp <;> ring

/-- T16 finite core: integrable outcomes are treated by truncation at M;
the empirical tail average is retained explicitly in the bound. -/
theorem outcome_tail_weight_bound {n : ℕ} (s Y : Fin (n+1) → ℝ)
    (c b M : ℝ) (hb : 0 < b) (hs : ∀ i, b ≤ s i) (hM : 0 < M) :
    (∑ i, weightChange (s i) c * |Y i|)/(n+1) ≤
      (1/b) * (M * ((belowCount s c : ℝ)/(n+1)) +
        (∑ i, if M < |Y i| then |Y i| else 0)/(n+1)) := by
  have hn : (0 : ℝ) < n+1 := by positivity
  have hpoint : ∀ i, weightChange (s i) c * |Y i| ≤
      (1/b)*(M*(if s i < c then 1 else 0) + (if M < |Y i| then |Y i| else 0)) := by
    intro i
    have hw := weight_change_bound (s i) c b hb (hs i)
    by_cases hsc : s i < c
    · have hwb : weightChange (s i) c ≤ 1/b := by simpa [hsc] using hw.2
      have hY : |Y i| ≤ M + (if M < |Y i| then |Y i| else 0) := by
        split_ifs <;> linarith
      have ha := mul_le_mul_of_nonneg_right hwb (abs_nonneg (Y i))
      have ht := mul_le_mul_of_nonneg_left hY (one_div_pos.mpr hb).le
      simpa [hsc] using ha.trans ht
    · have ht : (0 : ℝ) ≤ if M < |Y i| then |Y i| else 0 := by
        split_ifs <;> positivity
      simp only [weightChange, max_eq_left (le_of_not_gt hsc), sub_self,
        zero_mul, if_neg hsc, mul_zero, zero_add]
      exact mul_nonneg (one_div_pos.mpr hb).le ht
  have hsum : (∑ i, weightChange (s i) c * |Y i|) ≤
      (1/b)*(M*(belowCount s c : ℝ) + ∑ i, if M < |Y i| then |Y i| else 0) := by
    calc
      (∑ i, weightChange (s i) c * |Y i|) ≤
          ∑ i, (1/b)*(M*(if s i < c then 1 else 0) +
            (if M < |Y i| then |Y i| else 0)) :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = (1/b)*(M*(belowCount s c : ℝ) + ∑ i, if M < |Y i| then |Y i| else 0) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [belowCount]
  calc
    (∑ i, weightChange (s i) c * |Y i|)/(n+1) ≤
        ((1/b)*(M*(belowCount s c : ℝ) + ∑ i, if M < |Y i| then |Y i| else 0))/(n+1) :=
      div_le_div_of_nonneg_right hsum hn.le
    _ = (1/b)*(M*((belowCount s c : ℝ)/(n+1)) +
        (∑ i, if M < |Y i| then |Y i| else 0)/(n+1)) := by ring

/-- T16 finite core: exact difference of ratios, used after bounding the
changes in weighted numerator and first stage. Both denominators are nonzero. -/
theorem ratio_perturbation (J J' H H' : ℝ) (hH : H ≠ 0) (hH' : H' ≠ 0) :
    J'/H' - J/H = ((J'-J)*H - J*(H'-H))/(H'*H) := by
  field_simp <;> ring

/-- T17(a): setting always-taker probability to zero in equation (7) gives
the corrected PRODUCT of the two Bernoulli factors, footnote 3 p. 497. -/
theorem one_sided_unit_likelihood (π : ℝ) (z d : Bool) :
    bernoulliFactor (nestedReceipt π 0 z) d = bernoulliFactor (π * bit z) d := by
  simp [nestedReceipt]

/-- T17(b): controls contribute 1, so the corrected likelihood is exactly
the binomial-regression likelihood on Z=1 observations. Consequently its
maximizers for any parameterized π are the same. -/
theorem one_sided_likelihood_reduction {I : Type*} [Fintype I]
    (π : I → ℝ) (Z D : I → Bool) (hside : ∀ i, Z i = false → D i = false) :
    (∏ i, bernoulliFactor (π i * bit (Z i)) (D i)) =
      ∏ i ∈ Finset.univ.filter (fun i => Z i = true), bernoulliFactor (π i) (D i) := by
  classical
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  cases hz : Z i
  · rw [hside i hz]
    simp [bit, bernoulliFactor]
  · simp [bit]

/-- T17(c): the printed plus sign is not the Bernoulli likelihood. At π=3/4
and Z=1 it gives 7/4 or 5/4, instead of 3/4 or 1/4. -/
theorem printed_one_sided_factor_countercheck :
    ((3/4 : ℝ)^1 + (1-3/4)^0 = 7/4) ∧
    ((3/4 : ℝ)^0 + (1-3/4)^1 = 5/4) ∧
    bernoulliFactor (3/4) true = 3/4 ∧ bernoulliFactor (3/4) false = 1/4 := by
  norm_num [bernoulliFactor]

/-- T18(iv): the nested receipt probability is strictly between 0 and 1
when BOTH probit probabilities are, as required by equations (5)-(6). -/
theorem nested_probability_range (a b : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) (z : Bool) :
    nestedReceipt a b z ∈ Ioo (0 : ℝ) 1 ∧
      nestedReceipt a b z = if z then a else a*b := by
  cases z <;> simp only [nestedReceipt, bit, Bool.false_eq_true, if_false, if_true,
    mul_zero, zero_add, mul_one]
  · refine ⟨⟨mul_pos ha.1 hb.1, ?_⟩, trivial⟩
    exact lt_trans (mul_lt_of_lt_one_right ha.1 hb.2) ha.2
  · have heq : a * (1-b) + a*b = a := by ring
    rw [heq]
    exact ⟨ha,rfl⟩

/-- T14(a)/T18: every ordered interior pair of receipt rates 0<q<p<1
has nested parameters P_AC=p and P_A|AC=q/p, both in (0,1), and the
receipt difference is p-q. This is the saturated interior parameterization. -/
theorem nested_receipt_parameters (p q : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p < 1) :
    p ∈ Ioo (0 : ℝ) 1 ∧ q/p ∈ Ioo (0 : ℝ) 1 ∧
    nestedReceipt p (q/p) false = q ∧ nestedReceipt p (q/p) true = p ∧
    p*(1-q/p) = p-q := by
  have hp0 : 0 < p := lt_trans hq hqp
  refine ⟨⟨hp0,hp⟩, ⟨div_pos hq hp0, (div_lt_one hp0).2 hqp⟩, ?_, ?_, ?_⟩
  all_goals try dsimp [nestedReceipt, bit]
  all_goals field_simp [hp0.ne'] <;> ring

/-- T18(i), exact Boolean partition underlying the two-sided receipt model:
without defiers, compliers and always-takers partition D₁=1. -/
theorem compliance_type_partition {X : Type*} (u : PotentialUnit X) (h : ¬ u.defier) :
    ¬ (u.complier ∧ u.d0 = true) ∧
    (u.complier ∨ u.d0 = true ↔ u.d1 = true) := by
  rcases u with ⟨x,d0,d1,y0,y1⟩
  cases d0 <;> cases d1 <;> simp_all [PotentialUnit.complier, PotentialUnit.defier]

/-- T18(v): the equation (9) integrand cancels the positive conditional
compliance score to the conditional complier effect, giving equation (10). -/
theorem corrected_equation_nine_integrand (p μ : ℝ) (hp : 0 < p) :
    (p*μ)/p = μ := by
  field_simp [ne_of_gt hp]

/-- T19: indicator of a positive latent index, corrected supplement A1-A2.
The >0 predicate is explicit, as in the deposited code. -/
def positiveIndicator (index : ℝ) : ℝ := if 0 < index then 1 else 0

/-- "ACᵢ = I[latent index > 0]", corrected supplement A1-A2 (T19). -/
def latentAC (indexAC : ℝ) : ℝ := positiveIndicator indexAC

/-- "Aᵢ = I[latent index > 0] ACᵢ", corrected supplement A1-A2 (T19). -/
def latentA (indexAC indexA : ℝ) : ℝ := positiveIndicator indexA * latentAC indexAC

/-- "Cᵢ = ACᵢ - Aᵢ", supplement A1, retained by the correction (T19). -/
def latentC (indexAC indexA : ℝ) : ℝ := latentAC indexAC - latentA indexAC indexA

/-- "Dᵢ = CᵢZᵢ + Aᵢ", corrected supplement A1 (T19). -/
def latentD (indexAC indexA : ℝ) (z : Bool) : ℝ :=
  latentC indexAC indexA * bit z + latentA indexAC indexA


/-- T19(i)-(ii): for ALL real latent indices the corrected recipe gives
binary receipt, mutually exclusive A/C, and monotone potential treatments.
This covers both the baseline and nonlinear designs and any realization. -/
theorem corrected_simulation_types (iAC iA : ℝ) (z : Bool) :
    (latentAC iAC = 0 ∨ latentAC iAC = 1) ∧
    (latentA iAC iA = 0 ∨ latentA iAC iA = 1) ∧
    (latentC iAC iA = 0 ∨ latentC iAC iA = 1) ∧
    latentA iAC iA ≤ latentAC iAC ∧ latentA iAC iA * latentC iAC iA = 0 ∧
    (latentD iAC iA z = 0 ∨ latentD iAC iA z = 1) ∧
    latentD iAC iA true - latentD iAC iA false = latentC iAC iA ∧
    0 ≤ latentC iAC iA ∧
    (latentD iAC iA false = 1 ↔ latentA iAC iA = 1) ∧
    (latentD iAC iA false = 0 ∧ latentD iAC iA true = 1 ↔ latentC iAC iA = 1) ∧
    (latentD iAC iA false = 0 ∧ latentD iAC iA true = 0 ↔ latentAC iAC = 0) := by
  by_cases hac : 0 < iAC <;> by_cases ha : 0 < iA <;> cases z <;>
    norm_num [latentAC, latentA, latentC, latentD, positiveIndicator, bit, hac, ha]

/-- T19(iii): the printed self-referential treatment equation has no solution
for an assigned always-taker, two solutions for A=0,Z=1, and D=A for Z=0. -/
theorem printed_simulation_equation_failure :
    (¬ ∃ D : ℝ, D = D*1 + 1) ∧
    ((0 : ℝ) = 0*1+0 ∧ (1 : ℝ) = 1*1+0) ∧
    (∀ D A : ℝ, D = D*0+A ↔ D = A) := by
  constructor
  · rintro ⟨D,hD⟩; linarith
  constructor
  · norm_num
  · intro D A; simp

/-- T19(iv): the printed outcome Y=Y₀+τD matches exclusion/SUTVA when
Y₁=Y₀+τ. The correction changes the treatment recipe, not the outcome equation. -/
theorem simulation_outcome_identity (Y0 τ D : ℝ) :
    Y0 + τ*D = Y0 + D*((Y0+τ)-Y0) := by ring

/-- Section 3.3 weighted sample arm mean, p. 498. This also defines equation
(4) when wᵢ=1. Positive arm sums are required wherever the estimator is used. -/
def sampleArm {n : ℕ} (w Y : Fin n → ℝ) (Z : Fin n → Bool) (z : Bool) : ℝ :=
  (∑ i, w i * (if Z i = z then Y i else 0)) /
    (∑ i, w i * (if Z i = z then 1 else 0))

/-- The ICSW sample estimator of Section 3.3, p. 498: weighted outcome arm
difference divided by weighted receipt arm difference, with an intercept. -/
def sampleWald {n : ℕ} (w Y : Fin n → ℝ) (D Z : Fin n → Bool) : ℝ :=
  (sampleArm w Y Z true - sampleArm w Y Z false) /
    (sampleArm w (fun i => bit (D i)) Z true - sampleArm w (fun i => bit (D i)) Z false)

/-- Multiplying every weight by a common nonzero constant preserves each
weighted sample arm mean (finite algebra, T26 L7). -/
theorem sample_arm_scale {n : ℕ} (w Y : Fin n → ℝ) (Z : Fin n → Bool)
    (z : Bool) (k : ℝ) (hk : k ≠ 0) :
    sampleArm (fun i => k*w i) Y Z z = sampleArm w Y Z z := by
  unfold sampleArm
  have hnum : (∑ i, k*w i*(if Z i = z then Y i else 0)) =
      k * ∑ i, w i*(if Z i = z then Y i else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hden : (∑ i, k*w i*(if Z i = z then 1 else 0)) =
      k * ∑ i, w i*(if Z i = z then 1 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hnum,hden]
  exact mul_div_mul_left _ _ hk

/-- T26 L7: ICSW is unchanged by a common positive weight scale. -/
theorem sample_wald_scale {n : ℕ} (w Y : Fin n → ℝ) (D Z : Fin n → Bool)
    (k : ℝ) (hk : 0 < k) :
    sampleWald (fun i => k*w i) Y D Z = sampleWald w Y D Z := by
  unfold sampleWald
  simp_rw [sample_arm_scale w _ Z _ k (ne_of_gt hk)]

/-- T27(c): if all estimated compliance scores are the same positive number,
ICSW equals equation (4) EXACTLY for each sample with defined arm means and
nonzero first stage. The equality even extends to Lean's totalized division. -/
theorem constant_scores_equal_iv {n : ℕ} (Y : Fin n → ℝ) (D Z : Fin n → Bool)
    (p : ℝ) (hp : 0 < p) :
    sampleWald (fun _ => 1/p) Y D Z = sampleWald (fun _ => 1) Y D Z := by
  simpa using sample_wald_scale (fun _ => 1) Y D Z (1/p) (one_div_pos.mpr hp)

/-- Centered IV cross-product for equation (4) as bivariate 2SLS, p. 495. -/
def sampleCross {n : ℕ} (Z : Fin n → Bool) (V : Fin n → ℝ) : ℝ :=
  ∑ i, (bit (Z i) - (∑ j, bit (Z j))/n) * (V i - (∑ j, V j)/n)

/-- T25 finite core: the centered cross-product is its exact raw-sum
expression, with the empirical means and the full sample size retained. -/
theorem sample_cross_raw {n : ℕ} (Z : Fin n → Bool) (V : Fin n → ℝ)
    (hn : (n : ℝ) ≠ 0) :
    sampleCross Z V = (∑ i, bit (Z i)*V i) - ((∑ i, bit (Z i))/n)*(∑ i, V i) := by
  unfold sampleCross
  simp_rw [sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hn] <;> ring

/-- T25 finite core: the unweighted arm means equal the empirical assigned
and control totals divided by their actual arm counts. -/
theorem sample_arm_unweighted_raw {n : ℕ} (Z : Fin n → Bool) (V : Fin n → ℝ) :
    sampleArm (fun _ => 1) V Z true = (∑ i, bit (Z i)*V i)/(∑ i, bit (Z i)) ∧
    sampleArm (fun _ => 1) V Z false =
      ((∑ i, V i)-(∑ i, bit (Z i)*V i))/((n : ℝ)-(∑ i, bit (Z i))) := by
  have ht (i : Fin n) : (if Z i = true then V i else 0) = bit (Z i)*V i := by
    cases Z i <;> simp [bit]
  have htc (i : Fin n) : (if Z i = true then (1 : ℝ) else 0) = bit (Z i) := by
    cases Z i <;> simp [bit]
  have hf (i : Fin n) : (if Z i = false then V i else 0) = V i-bit (Z i)*V i := by
    cases Z i <;> simp [bit]
  have hfc (i : Fin n) : (if Z i = false then (1 : ℝ) else 0) = 1-bit (Z i) := by
    cases Z i <;> simp [bit]
  constructor
  · simp [sampleArm,ht,htc]
  · simp [sampleArm,hf,hfc,Finset.sum_sub_distrib]

/-- T25 finite algebra behind the preceding sample identity, expressed in
raw sums (N, assigned count, total and assigned outcome/receipt sums). -/
theorem bivariate_ratio_algebra (N nZ sY sZY sD sZD : ℝ)
    (hN : N ≠ 0) (hZ : nZ ≠ 0) (h0 : N-nZ ≠ 0)
    (hstage : N*sZD - nZ*sD ≠ 0) :
    (sZY/nZ - (sY-sZY)/(N-nZ)) / (sZD/nZ - (sD-sZD)/(N-nZ)) =
      (sZY - (nZ/N)*sY)/(sZD - (nZ/N)*sD) := by
  have hraw (s sZ : ℝ) : sZ/nZ-(s-sZ)/(N-nZ) =
      (N*sZ-nZ*s)/(nZ*(N-nZ)) := by
    field_simp [hZ,h0] <;> ring
  have hcenter (s sZ : ℝ) : sZ-(nZ/N)*s = (N*sZ-nZ*s)/N := by
    field_simp [hN] <;> ring
  rw [hraw sY sZY, hraw sD sZD, hcenter sY sZY, hcenter sD sZD,
    div_div_div_cancel_right₀ (mul_ne_zero hZ h0), div_div_div_cancel_right₀ hN]

/-- T25 equation (4) is the centered IV/2SLS coefficient with an intercept,
for every finite sample satisfying the stated arm and relevance conditions. -/
theorem sample_wald_bivariate_2sls {n : ℕ} (Y : Fin n → ℝ) (D Z : Fin n → Bool)
    (hn1 : 0 < ∑ i, bit (Z i)) (hn0 : (∑ i, bit (Z i)) < (n : ℝ))
    (hstage : sampleArm (fun _ => 1) (fun i => bit (D i)) Z true -
      sampleArm (fun _ => 1) (fun i => bit (D i)) Z false ≠ 0) :
    sampleWald (fun _ => 1) Y D Z = sampleCross Z Y / sampleCross Z (fun i => bit (D i)) := by
  have hN : (n : ℝ) ≠ 0 := ne_of_gt (lt_trans hn1 hn0)
  have hZ : (∑ i, bit (Z i)) ≠ 0 := hn1.ne'
  have h0 : (n : ℝ)-(∑ i, bit (Z i)) ≠ 0 := (sub_pos.mpr hn0).ne'
  have hstageRaw : (n : ℝ)*(∑ i, bit (Z i)*bit (D i)) -
      (∑ i, bit (Z i))*(∑ i, bit (D i)) ≠ 0 := by
    intro h
    apply hstage
    rw [(sample_arm_unweighted_raw Z (fun i => bit (D i))).1,
      (sample_arm_unweighted_raw Z (fun i => bit (D i))).2]
    field_simp [hZ,h0]
    nlinarith [h]
  unfold sampleWald
  rw [(sample_arm_unweighted_raw Z Y).1, (sample_arm_unweighted_raw Z Y).2,
    (sample_arm_unweighted_raw Z (fun i => bit (D i))).1,
    (sample_arm_unweighted_raw Z (fun i => bit (D i))).2,
    sample_cross_raw Z Y hN, sample_cross_raw Z (fun i => bit (D i)) hN]
  exact bivariate_ratio_algebra _ _ _ _ _ _ hN hZ h0 hstageRaw

/-- T25 worked example, pp. 497-498: ATE=1/2, LATE=2/17 (which rounds to
0.12), and the inverse-score weighted ratio recovers 1/2. -/
theorem gender_worked_example :
    ((1/2*0 + 1/2*1)/(1/2+1/2) : ℝ) = 1/2 ∧
    ((1/2*(3/4)*0 + 1/2*(1/10)*1)/(1/2*(3/4)+1/2*(1/10)) : ℝ) = 2/17 ∧
    (115/1000 : ℝ) ≤ 2/17 ∧ (2/17 : ℝ) < 125/1000 ∧
    ((1/2*(3/4)*(1/(3/4))*0 + 1/2*(1/10)*(1/(1/10))*1)/
      (1/2*(3/4)*(1/(3/4)) + 1/2*(1/10)*(1/(1/10))) : ℝ) = 1/2 := by
  norm_num

/-- Finite covariate-density average used by equations (8)-(14). f is the
population covariate mass, p the true score, μ the conditional complier effect. -/
def profileRatio {X : Type*} [Fintype X] (f p μ w : X → ℝ) : ℝ :=
  (∑ x, f x*w x*p x*μ x)/(∑ x, f x*w x*p x)

/-- T4(iii), T26 L2-L5 and T27 L2: positive true scores cancel term by term
from the actual finite covariate sums in the Appendix. -/
theorem profile_inverse_score_cancellation {X : Type*} [Fintype X]
    (f p μ : X → ℝ) (hf : ValidLaw f) (hp : ∀ x, 0 < p x) :
    (∑ x, f x*(1/p x)*p x) = 1 ∧
    (∑ x, f x*(1/p x)*p x*μ x) = fE f μ ∧
    profileRatio f p μ (fun x => 1/p x) = fE f μ := by
  have hden : (∑ x, f x*(1/p x)*p x) = 1 := by
    calc
      _ = ∑ x, f x := by
        apply Finset.sum_congr rfl
        intro x _; field_simp [ne_of_gt (hp x)]
      _ = 1 := hf.2
  have hnum : (∑ x, f x*(1/p x)*p x*μ x) = fE f μ := by
    apply Finset.sum_congr rfl
    intro x _; field_simp [ne_of_gt (hp x)]
  refine ⟨hden,hnum,?_⟩
  unfold profileRatio
  try dsimp only
  rw [hnum,hden,div_one]

/-- T4(iv): exact finite covariance gap between the unweighted and true-score
weighted limits. -/
theorem profile_covariance_gap {X : Type*} [Fintype X] (f p μ : X → ℝ)
    (hden : fE f p ≠ 0) :
    (fE f (fun x => p x*μ x))/(fE f p) - fE f μ = fCov f p μ / fE f p := by
  unfold fCov
  field_simp <;> ring

/-- Average inverse compliance weight w̄c, Appendix p. 504. -/
def profileAverageWeight {X : Type*} [Fintype X] (f p : X → ℝ) : ℝ := ∑ x, f x / p x

/-- T26 L2-L5: the corrected (9)-(10), (13), and (14) finite identities;
under Assumption 1 the finite conditional-mean average is the ATE. -/
theorem appendix_finite_identities {X : Type*} [Fintype X]
    (f p μ a : X → ℝ) (hf : ValidLaw f) (hp : ∀ x, 0 < p x)
    (hw : profileAverageWeight f p ≠ 0) :
    ((∑ x, ((p x*μ x)/p x)*f x)/profileAverageWeight f p) =
      fE f μ/profileAverageWeight f p ∧
    ((∑ x, (p x/p x)*f x)/profileAverageWeight f p) =
      1/profileAverageWeight f p ∧
    (fE f μ/profileAverageWeight f p)/(1/profileAverageWeight f p) = fE f μ ∧
    ((∀ x, μ x = a x) → fE f μ = fE f a) := by
  have hnum : (∑ x, ((p x*μ x)/p x)*f x) = fE f μ := by
    apply Finset.sum_congr rfl
    intro x _; field_simp [ne_of_gt (hp x)] <;> ring
  have hden : (∑ x, (p x/p x)*f x) = 1 := by
    have hterm : ∀ x, (p x/p x)*f x = f x := by
      intro x; simp [ne_of_gt (hp x)]
    simpa only [hterm] using hf.2
  refine ⟨by rw [hnum], by rw [hden], ?_, ?_⟩
  · field_simp
  · intro h
    unfold fE
    apply Finset.sum_congr rfl
    intro x _
    rw [h x]

/-- T27(a), finite Bayes/averaging lemma: g(x)=f(x)p(x)/Pr(C) is the
complier covariate distribution, and averaging μ against g gives the LATE
profile ratio. -/
theorem complier_profile_bayes {X : Type*} [Fintype X] (f p μ : X → ℝ)
    (hf : ValidLaw f) (hp : ∀ x, 0 ≤ p x) (hC : 0 < fE f p) :
    ValidLaw (fun x => f x*p x/fE f p) ∧
    fE (fun x => f x*p x/fE f p) μ = fE f (fun x => p x*μ x)/fE f p := by
  constructor
  · constructor
    · intro x; exact div_nonneg (mul_nonneg (hf.1 x) (hp x)) hC.le
    · rw [← Finset.sum_div]
      exact div_self (ne_of_gt hC)
  · unfold fE
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    apply congrArg (fun t : ℝ => t / (∑ x, f x*p x))
    apply Finset.sum_congr rfl
    intro x _; ring

/-- The σ-algebra generated by pretreatment covariates, p. 496. -/
def covariateSigma {Ω X : Type*} [MeasurableSpace X] (U : Ω → PotentialUnit X) :
    MeasurableSpace Ω := MeasurableSpace.comap (fun ω => (U ω).x) inferInstance

/-- General versions of P_C(x) and E(τ|C,X=x), pp. 496 and 499. The first
identity is E(1_C|X)=P_C(X), and the second is E(1_C τ|X)=P_C(X)μ(X).
These are conditional expectations on the actual probability law, NOT free
functions or a zero measure. Equalities hold up to null sets, as usual for
conditional expectations; finite-profile statements above use literal events. -/
def ScoreVersions {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialUnit X) (c m : X → ℝ) : Prop :=
  Measurable c ∧ Measurable m ∧
  (fun ω => c (U ω).x) =ᵐ[μ]
    condExp (covariateSigma U) μ (fun ω => if (U ω).complier then (1 : ℝ) else 0) ∧
  (fun ω => c (U ω).x * m (U ω).x) =ᵐ[μ]
    condExp (covariateSigma U) μ (fun ω => if (U ω).complier then (U ω).tau else 0)

/-- Assumption 1 in the general conditional-expectation formulation, p. 499.
It equates the actual conditional population effect with the complier effect. -/
def A1Versions {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialUnit X) (m : X → ℝ) : Prop :=
  (fun ω => m (U ω).x) =ᵐ[μ] condExp (covariateSigma U) μ (fun ω => (U ω).tau)

/-- Joint pretreatment and assignment variables for iid sampling, p. 494. -/
def jointVariables {Ω X : Type*} (U : Ω → PotentialUnit X) (Z : Ω → Bool) :
    Ω → (X × Bool × Bool × ℝ × ℝ) × Bool :=
  fun ω => (((U ω).x,(U ω).d0,(U ω).d1,(U ω).y0,(U ω).y1),Z ω)

/-- Uniform samplewise score error max_{i≤N}|P̂_Ci-P_Ci|, an
explicit sufficient regularity condition for T16/T26/T27. -/
def uniformScoreError {Ω X : Type*} (U : ℕ → Ω → PotentialUnit X)
    (c : X → ℝ) (s : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n+1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n))
    (fun i => |s n i ω - c (U i ω).x|)

/-- One explicit interpretation of "suitable regularity conditions",
pp. 498, 504-505. All rows are iid from a genuine probability law, satisfy
the five IV assumptions, have integrable potential outcomes, and have true
scores bounded below by one common ε>0. Estimated scores are in (0,1] and
their maximum error converges in probability to zero. The uniform condition
is a sufficient specification of the article's unlisted conditions;
it is not asserted to follow from pointwise Assumption 2 alone. -/
structure ICSWConditions {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : ℕ → Ω → PotentialUnit X) (Z : ℕ → Ω → Bool)
    (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ) : Prop where
  iv : ∀ i, IVAssumptions μ (U i) (Z i)
  independent : iIndepFun (fun i => jointVariables (U i) (Z i)) μ
  identical : ∀ i, IdentDistrib (jointVariables (U i) (Z i)) (jointVariables (U 0) (Z 0)) μ μ
  score : ∀ i, ScoreVersions μ (U i) c m
  overlap : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ᵐ ω ∂μ, ε < c (U i ω).x ∧ c (U i ω).x ≤ 1
  estimated_measurable : ∀ n i, Measurable (s n i)
  estimated_range : ∀ n, ∀ᵐ ω ∂μ, ∀ i : Fin (n+1), 0 < s n i.val ω ∧ s n i.val ω ≤ 1
  uniform_consistency : TendstoInMeasure μ (uniformScoreError U c s) atTop (fun _ => 0)

/-- The random ICSW estimator, Section 3.3 p. 498, with N=n+1 observations.
Finite-sample zero denominators are totalized only to define a sequence;
the consistency statements require the population first stage to be nonzero. -/
def icswSequence {Ω X : Type*} (U : ℕ → Ω → PotentialUnit X) (Z : ℕ → Ω → Bool)
    (s : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sampleWald (fun i : Fin (n+1) => 1/s n i.val ω)
    (fun i => (U i.val ω).outcome (Z i.val ω))
    (fun i => (U i.val ω).receipt (Z i.val ω)) (fun i => Z i.val ω)

/-- The Winsorized estimator, footnote 6 p. 498: replace each score below
the SAME sample quantile by that quantile, including ties correctly. -/
def winsorizedSequence {Ω X : Type*} (U : ℕ → Ω → PotentialUnit X) (Z : ℕ → Ω → Bool)
    (s : ℕ → ℕ → Ω → ℝ) (cutoff : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sampleWald (fun i : Fin (n+1) => 1/max (s n i.val ω) (cutoff n ω))
    (fun i => (U i.val ω).outcome (Z i.val ω))
    (fun i => (U i.val ω).receipt (Z i.val ω)) (fun i => Z i.val ω)


/-- The covariate distribution among compliers, g(x) on p. 499: the
pushforward of the normalized complier subpopulation measure. -/
def complierCovariateLaw {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialUnit X) : Measure X :=
  Measure.map (fun ω => (U ω).x)
    (ENNReal.ofReal ((mP μ {ω | (U ω).complier})⁻¹) • μ.restrict {ω | (U ω).complier})


/-- Conditional always-taker share among A or C, equation (6), p. 496. -/
def alwaysAmongAC {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialUnit X) (x : X) : ℝ :=
  mP μ {ω | (U ω).d0 = true ∧ (U ω).d1 = true ∧ (U ω).x = x} /
    mP μ {ω | (U ω).d1 = true ∧ (U ω).x = x}


/-- T2(a)-(b), corrected comparison: the two ignorability conditions are
not ordered in general, with BOTH directions witnessed under all five IV
assumptions by explicit six-atom laws. The one-sided qualification is separate. -/
theorem corrected_ignorability_incomparability :
    (FIV sixMass (liftUnit case1Unit) Prod.snd ∧
      fTypicalIgnorability sixMass (liftUnit case1Unit) Prod.snd () ∧
      ¬ fLatentIgnorability sixMass (liftUnit case1Unit)) ∧
    (FIV sixMass (liftUnit case2Unit) Prod.snd ∧
      fLatentIgnorability sixMass (liftUnit case2Unit) ∧
      ¬ fTypicalIgnorability sixMass (liftUnit case2Unit) Prod.snd ()) := by
  refine ⟨⟨ignorability_counterexample.1, ignorability_counterexample.2.1, ?_⟩,
    ⟨baseline_selection_counterexample.1, baseline_selection_counterexample.2.1, ?_⟩⟩
  · intro h
    have hh := h () (by norm_num [fP, sixMass, randomized, typeMass, liftUnit,
      case1Unit, Fintype.sum_prod_type, Fin.sum_univ_succ])
    norm_num [fCE, fP, fE, sixMass, randomized, typeMass, liftUnit,
      case1Unit, PotentialUnit.tau, PotentialUnit.complier,
      Fintype.sum_prod_type, Fin.sum_univ_succ] at hh
  · intro h
    norm_num [fTypicalIgnorability, fCE, fP, fE, sixMass, randomized, typeMass,
      liftUnit, case2Unit, PotentialUnit.receipt,
      Fintype.sum_prod_type, Fin.sum_univ_succ] at h

/-- T1(iii): the witness satisfies even FULL independence of (Y₀,Y₁) from
received treatment, a stronger condition than the two printed mean equalities. -/
theorem potential_pair_independent_of_receipt :
    FIndep sixMass (fun i => ((case1Unit i.1).y0, (case1Unit i.1).y1))
      (fun i => (case1Unit i.1).receipt i.2) := by
  rintro ⟨a,b⟩ d
  by_cases ha : a = 0 <;> by_cases hb0 : b = 0 <;> by_cases hb1 : b = 1 <;> cases d <;>
    norm_num [fP, sixMass, randomized, typeMass, case1Unit, PotentialUnit.receipt,
      Fintype.sum_prod_type, Fin.sum_univ_succ, ha, hb0, hb1]
  all_goals split_ifs <;> norm_num

/-- T3(B1): the conditional-independence witness is not marginally
independent of the full compliance type. -/
theorem conditional_witness_not_marginally_independent :
    ¬ FIndep conditionalJoint (fun i => i.1.1.2.1)
      (fun i => ((independenceUnit i.1).d0, (independenceUnit i.1).d1)) := by
  intro h
  have hh := h true (false,true)
  norm_num [fP, conditionalJoint, randomized, conditionalMass, independenceUnit,
    bit, Fintype.sum_prod_type, Fintype.sum_bool] at hh

/-- T3(A2): nested probabilities for both profiles are strictly interior,
so neither a boundary fit nor lack of overlap drives the counterexample. -/
theorem marginal_witness_nested_probabilities :
    fCE marginalJoint (fun i => bit (independenceUnit i.1).d1)
      (fun i => (independenceUnit i.1).x = false) = 7/10 ∧
    fCE marginalJoint (fun i => bit (independenceUnit i.1).d1)
      (fun i => (independenceUnit i.1).x = true) = 5/6 ∧
    fCE marginalJoint (fun i => bit (independenceUnit i.1).d0)
      (fun i => (independenceUnit i.1).d1 = true ∧ (independenceUnit i.1).x = false) = 3/7 ∧
    fCE marginalJoint (fun i => bit (independenceUnit i.1).d0)
      (fun i => (independenceUnit i.1).d1 = true ∧ (independenceUnit i.1).x = true) = 1/5 := by
  norm_num [fCE, fP, fE, marginalJoint, randomized, marginalMass, independenceUnit,
    bit, Fintype.sum_prod_type, Fintype.sum_bool]

/-- T18(iii): with one-sided noncompliance and true score 1/2, the receipt
probability averaged over Z is 1/4. The printed assignment-specific right
side is 0 or 1/2, so the dropped Z conditioning changes the quantity. -/
theorem receipt_conditioning_countercheck :
    let U : Bool × Bool → PotentialUnit Unit := fun i => ⟨(),false,i.1,0,1⟩
    let p := randomized (fun _ : Bool => (1/2 : ℝ)) (1/2)
    fP p (fun i => (U i).receipt i.2 = true) = 1/4 ∧
    fScore p U () = 1/2 ∧
    ((1/2 : ℝ)*bit false = 0) ∧ ((1/2 : ℝ)*bit true = 1/2) := by
  norm_num [fP, fScore, randomized, PotentialUnit.receipt, PotentialUnit.complier,
    bit, Fintype.sum_prod_type, Fintype.sum_bool]

/-- T5 support/admissibility checks: the explicit latent/observed uniform
values are inside their support, corrected thresholds give all compliers,
and the realized balanced assignment has exactly 250 treated records. -/
theorem rmse_witness_admissible :
    (-1 : ℝ) < 1/5 ∧ (1/5 : ℝ) < 1 ∧
    (∀ k : Fin 5, ∀ j : Fin 3, (-1 : ℝ) < noiseProfile k j ∧ noiseProfile k j < 1) ∧
    (∀ z, latentAC 2 = 1 ∧ latentA 2 (-2) = 0 ∧ latentC 2 (-2) = 1 ∧
      latentD 2 (-2) z = bit z) ∧
    (∑ i : RMSEIndex, bit i.2.2) = 250 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro k j; fin_cases k <;> fin_cases j <;> norm_num [noiseProfile]
  · intro z; cases z <;> norm_num [latentAC, latentA, latentC, latentD, positiveIndicator, bit]
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num [bit]

/-- T7(v)'s bootstrap perturbation: change only one W=0,Z=1 failure to t. -/
def bootstrapWeight (t : ℝ) (i : Bool × Bool × Fin 4) : ℝ :=
  if i.1 = false ∧ i.2.1 = true ∧ i.2.2.val = 1 then t else 1
def bootstrapRefitScores (t : ℝ) (x : Bool) : ℝ := if x then 3/4 else 1/(3+t)

/-- T7(v)/T8(c): refitting the compliance model changes the actual weighted
IV ratio to (t+11)/(t+7); holding scores fixed leaves it exactly 3/2 for
EVERY positive perturbation. This links the derivative witness to the data. -/
theorem bootstrap_refit_ratio (t : ℝ) (ht : 0 < t) :
    bootstrapRefitScores t false = 1/(3+t) ∧ bootstrapRefitScores t true = 3/4 ∧
    fWald (fun _ : Bool × Bool × Fin 4 => 1/16) oneSidedSample sampleZ
      (fun i => bootstrapWeight t i / unweightedScores i.1) = 3/2 ∧
    fWald (fun _ : Bool × Bool × Fin 4 => 1/16) oneSidedSample sampleZ
      (fun i => bootstrapWeight t i / bootstrapRefitScores t i.1) = (t+11)/(t+7) := by
  have h3 : 0 < t+3 := by linarith
  have h7 : 0 < t+7 := by linarith
  norm_num [fWald, fCE, fE, fP, oneSidedSample, sampleZ, bootstrapWeight,
    unweightedScores, bootstrapRefitScores, PotentialUnit.outcome, PotentialUnit.receipt,
    bit, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  constructor <;> field_simp <;> ring

/-- Conditioning independent finite randomization on its realized arm leaves
the latent-unit law unchanged. This is the finite probability step underlying
equation (3) and the weighted Appendix identities, pp. 495 and 504. -/
theorem randomized_conditional_mean {L : Type*} [Fintype L]
    (p : L → ℝ) (e : ℝ) (hp : ValidLaw p) (he0 : 0 < e) (he1 : e < 1)
    (v : L × Bool → ℝ) (z : Bool) :
    fCE (randomized p e) v (fun i => i.2 = z) = fE p (fun i => v (i,z)) := by
  have he : e ≠ 0 := ne_of_gt he0
  have hec : 1-e ≠ 0 := ne_of_gt (by linarith : 0 < 1-e)
  have hpSum := hp.2
  have hsum (k : ℝ) (u : L → ℝ) :
      (∑ i, p i*k*u i) = (∑ i, p i*u i)*k := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _; ring
  cases z <;>
    simp only [fCE, fE, fP, randomized, Fintype.sum_prod_type, Fintype.sum_bool,
      Bool.true_eq_false, Bool.false_eq_true, if_false, if_true, mul_zero,
      zero_add, add_zero]
  all_goals
    rw [hsum, ← Finset.sum_mul, hpSum]
    simp [he,hec]

/-- No-defier finite identity for each fixed unit: D(1)-D(0)=1_C and
Y(D(1))-Y(D(0))=1_C τ, the exact algebra of equation (3), p. 495. -/
theorem unit_itt_identities {X : Type*} (u : PotentialUnit X) (h : ¬ u.defier) :
    bit (u.receipt true) - bit (u.receipt false) = (if u.complier then 1 else 0) ∧
    u.outcome true - u.outcome false = (if u.complier then u.tau else 0) := by
  rcases u with ⟨x,d0,d1,y0,y1⟩
  cases d0 <;> cases d1 <;>
    simp_all [PotentialUnit.receipt, PotentialUnit.outcome, PotentialUnit.complier,
      PotentialUnit.defier, PotentialUnit.tau,bit]


/-- T15 complete counterexample: the explicit six-atom IV law satisfies
Assumption 1 and overlap, the oracle score error tends to zero, yet every
score quantile is 1/2 and the cutoff fails to tend to zero. Winsorization
changes neither the scores nor any finite-sample weighted Wald estimate. -/
theorem winsorization_cutoff_counterexample :
    FIV sixMass (liftUnit constantUnit) Prod.snd ∧
    fLatentIgnorability sixMass (liftUnit constantUnit) ∧
    fScore sixMass (liftUnit constantUnit) () = 1/2 ∧
    (1/4 : ℝ) < fScore sixMass (liftUnit constantUnit) () ∧
    fE sixMass (fun i => (constantUnit i.1).tau) = 1 ∧
    fWald sixMass (liftUnit constantUnit) Prod.snd (fun _ => 2) = 1 ∧
    Tendsto (fun _ : ℕ => |(1/2 : ℝ)-fScore sixMass (liftUnit constantUnit) ()|)
      atTop (𝓝 0) ∧
    ¬ Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 0) ∧
    (∀ n (level : ℝ), level ∈ Icc (0 : ℝ) 1 →
      Type7Quantile (fun _ : Fin (n+1) => (1/2 : ℝ)) level (1/2)) ∧
    (∀ n (Y : Fin (n+1) → ℝ) (D Z : Fin (n+1) → Bool),
      sampleWald (fun _ => 1/max (1/2 : ℝ) (1/2)) Y D Z =
        sampleWald (fun _ => 1/(1/2 : ℝ)) Y D Z) := by
  rcases constant_score_counterexample_law with ⟨hiv,hA1,hscore,hover,hate,hwal⟩
  refine ⟨hiv,hA1,hscore,hover,hate,hwal,?_,cutoff_not_zero.1,
    cutoff_not_zero.2.1,?_⟩
  · rw [hscore]
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · intro n Y D Z; simp

/-- T13 complete counterexample: all five IV assumptions, Assumption 1
and overlap hold in the constant-effect law. Its receipt probabilities are
3/4 and 1/4. For one independent observation per arm, the certified closed
ML fits have expected score 9/16, whereas the true score is 1/2. -/
theorem saturated_ml_bias_full_counterexample :
    FIV sixMass (liftUnit constantUnit) Prod.snd ∧
    fLatentIgnorability sixMass (liftUnit constantUnit) ∧
    fScore sixMass (liftUnit constantUnit) () = 1/2 ∧
    (1/4 : ℝ) < fScore sixMass (liftUnit constantUnit) () ∧
    fCE sixMass (fun i => bit ((constantUnit i.1).receipt i.2)) (fun i => i.2 = true) = 3/4 ∧
    fCE sixMass (fun i => bit ((constantUnit i.1).receipt i.2)) (fun i => i.2 = false) = 1/4 ∧
    ValidLaw twoObservationLaw ∧
    (∀ d, twoObservationFit d ∈ receiptTriangle ∧
      ∀ v ∈ receiptTriangle, twoObservationLikelihood d v.1 v.2 ≤
        twoObservationLikelihood d (twoObservationFit d).1 (twoObservationFit d).2) ∧
    fE twoObservationLaw (fun d => (twoObservationFit d).1-(twoObservationFit d).2) = 9/16 ∧
    (9/16 : ℝ) ≠ fScore sixMass (liftUnit constantUnit) () := by
  rcases constant_score_counterexample_law with ⟨hiv,hA1,hscore,hover,hate,hwal⟩
  refine ⟨hiv,hA1,hscore,hover,?_,?_,saturated_unbiasedness_counterexample.1,
    two_observation_ml_maxima,saturated_unbiasedness_counterexample.2.2.1,?_⟩
  · norm_num [fCE,fE,fP,sixMass,randomized,typeMass,constantUnit,bit,
      PotentialUnit.receipt,Fintype.sum_prod_type,Fin.sum_univ_succ]
  · norm_num [fCE,fE,fP,sixMass,randomized,typeMass,constantUnit,bit,
      PotentialUnit.receipt,Fintype.sum_prod_type,Fin.sum_univ_succ]
  · rw [hscore]; norm_num

end
end AronowAudit.P029

