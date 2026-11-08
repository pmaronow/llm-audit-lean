import Mathlib
import SAP.P043.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P043

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

/-- The finite product law is a probability law, assignment has mass one half
in each arm, and assignment is independent of every latent-population event. -/
def FairAssignmentClaims {Ω : Type*} [Fintype Ω] (P : Population Ω) : Prop :=
  (∀ z, armProb (1/2) z = 1/2) ∧
  (∀ z i, 0 ≤ jointMass P (1/2) z i) ∧
  (∑ z : Bool, ∑ i, jointMass P (1/2) z i) = 1 ∧
  (∀ z, (∑ i, jointMass P (1/2) z i) = 1/2) ∧
  (∀ (A : Ω → Prop) z,
    (∑ i, jointMass P (1/2) z i * indicator (A i)) =
      armProb (1/2) z * eventProb P A)

/-- Exclusion at every dose and assignment, and consistency of both observed
variables with the potential knowledge and support response. -/
def IVConsistencyClaims {Ω : Type*} (m : IVModel Ω) : Prop :=
  (∀ z k i, ivPotentialSupport m z k i = m.response k i) ∧
  (∀ z i, ivKnowledge m z i = (m.knowledge z i : ℝ) ∧
    ivOutcome m z i = ivPotentialSupport m z (m.knowledge z i) i)

/-- A pair consisting of an increaser and an integer margin crossed upwards
in the two-type witness. The crossing condition forces the margin to be 9,
so natural-number subtraction in `doseIncrement` is used only at a positive margin. -/
def UpDownCrossedMargin (x : Bool × ℕ) : Prop :=
  increaser upDownWitness x.1 ∧
  upDownWitness.knowledge false x.1 < x.2 ∧
  x.2 ≤ upDownWitness.knowledge true x.1

/-- Every crossed increaser increment is one. Consequently every finite
normalized nonnegative average, and every probability-weighted average, is one
and differs from the IV ratio. Integrability is a conclusion, not an extra
assumption on the weighting. The measure formulation covers arbitrary weights
on type-margin pairs, including countably supported weights. -/
def UpDownAverageClaims : Prop :=
  (∀ x, UpDownCrossedMargin x → x.2 = 9 ∧ doseIncrement upDownWitness x.2 x.1 = 1) ∧
  (∀ (n : ℕ) (x : Fin n → Bool × ℕ) (w : Fin n → ℝ),
    (∀ a, 0 ≤ w a) → (∀ a, UpDownCrossedMargin (x a)) → (∑ a, w a) = 1 →
    (∑ a, w a * doseIncrement upDownWitness (x a).2 (x a).1) = 1 ∧
    (∑ a, w a * doseIncrement upDownWitness (x a).2 (x a).1) ≠
      ivRatio upDownPopulation (1/2) upDownWitness) ∧
  (∀ (ν : Measure (Bool × ℕ)) [IsProbabilityMeasure ν],
    (∀ᵐ x ∂ν, UpDownCrossedMargin x) →
    Integrable (fun x => doseIncrement upDownWitness x.2 x.1) ν ∧
    (∫ x, doseIncrement upDownWitness x.2 x.1 ∂ν) = 1 ∧
    (∫ x, doseIncrement upDownWitness x.2 x.1 ∂ν) ≠
      ivRatio upDownPopulation (1/2) upDownWitness)

/-- Conditional average support change per unit of knowledge among increasers.
Only increasers contribute to the numerator; their real knowledge difference
is strictly positive. The whole statement certifies positive conditioning
probabilities and unit knowledge differences in the models where this is used. -/
def increaserPerUnitEffect {Ω : Type*} [Fintype Ω]
    (P : Population Ω) (m : IVModel Ω) : ℝ := by
  classical
  exact eventMean P (increaser m) (fun i => if increaser m i then
    (m.response (m.knowledge true i) i - m.response (m.knowledge false i) i) /
      ((m.knowledge true i : ℝ) - (m.knowledge false i : ℝ)) else 0)

/-- P043-T1; p. 474 (PDF p. 12), below Table 4, referring to p. 473 (PDF p. 11).
The two specified validator constructions are exact randomized counterexamples
to an unconditional mediation comparison. In the linear construction all eight
states have mass 1/8, knowledge increases by 6/5, support increases by h/20 with
knowledge, M=3/50 and D=-3/50, and observed support cancels assignment pointwise.
Both arm laws, all covariances, population regression slopes, and structural
coefficient identities are as specified. In the integer construction all 1000
states have mass 1/1000; K(0)=8 and K(1)=9 for W<=4 or 10 for W=5, with W stored
as i.1.val+1. Knowledge, support and constant general knowledge respect the 2007
index ranges. All stated arm means, nested means and one-unit effects hold;
both support arm means are 59/25 and both support laws put mass 9/25 at 3.
In each construction D<0, M>0 and tau=0<M, so the design alone gives neither
tau>=M nor the null inference M<=0. The contextual comparison assuming D>=0
is not refuted. The usual measure-theoretic conditions are assumed; the
specified probability spaces are finite and all expectations exist. -/
def T1WholeStatement : Prop :=
  T1Statement ∧
  FairAssignmentClaims linearPopulation ∧
  FairAssignmentClaims integerPopulation ∧
  (∀ t i, observedSupport linearWitness t i =
    23/10 + linearU₁ i / 20 + linearU₂ i) ∧
  linearWitness = linearModel 8 (6/5) (19/10) (1/20) (-3/50) linearU₁ linearU₂ ∧
  (∀ i : Fin 5 × Fin 100,
    integerWitness.knowledge false i = 8 ∧
    integerWitness.knowledge true i = (if i.1.val = 4 then 10 else 9) ∧
    (i.1.val + 1 ≤ 4 → integerWitness.knowledge true i = 9) ∧
    (i.1.val + 1 = 5 → integerWitness.knowledge true i = 10)) ∧
  (∀ t i, 0 ≤ integerWitness.knowledge t i ∧ integerWitness.knowledge t i ≤ 15 ∧
    0 ≤ observedSupport integerWitness t i ∧ observedSupport integerWitness t i ≤ 3 ∧
    0 ≤ integerGeneralKnowledge t i ∧ integerGeneralKnowledge t i ≤ 5) ∧
  (∀ t, armMean integerPopulation (1/2) t (observedSupport integerWitness) = 59/25) ∧
  (direct linearPopulation linearWitness < 0 ∧ direct integerPopulation integerWitness < 0) ∧
  (¬ reducedForm linearPopulation (1/2) linearWitness ≥ mediated linearPopulation linearWitness) ∧
  (¬ reducedForm integerPopulation (1/2) integerWitness ≥ mediated integerPopulation integerWitness) ∧
  (¬ (reducedForm linearPopulation (1/2) linearWitness = 0 →
    mediated linearPopulation linearWitness ≤ 0)) ∧
  (¬ (reducedForm integerPopulation (1/2) integerWitness = 0 →
    mediated integerPopulation integerWitness ≤ 0))

/-- P043-T4; p. 472 (PDF p. 10) and pp. 474-475 (PDF pp. 12-13).
The specified two-type and two five-type validator constructions satisfy fair
independent assignment, exclusion, consistency and a strictly positive first
stage. The two-type witness has the stated arm means and covariances, zero IV
and covariance ratios, increaser mass 2/3 and increaser effect one. Every increaser
crosses only margin 9 with increment one; every normalized nonnegative average
of these increments is one, different from the zero IV ratio. This includes
arbitrary probability averages, whose integrability is certified. Cancellation
explains the zero reduced form, and responses are nondecreasing with the stated
2008 index bounds. The five-type models have the specified complete conditional
and joint observable laws, common positive first stage 1/5 and zero reduced
form and IV ratio, but increaser probabilities 2/5 and 3/5 and effects one and
4/3 respectively. Every increase is one unit, so these are also the average
per-unit effects. No functional of the observable law recovers the increaser
effect in both admissible models, hence none works on the entire claimed class.
These are validator witnesses, not empirical claims about the curriculum.
The usual measure-theoretic conditions are assumed; all finite expectations
exist and every conditioning or ratio denominator used here is positive. -/
def T4WholeStatement : Prop :=
  T4Statement ∧
  FairAssignmentClaims upDownPopulation ∧
  FairAssignmentClaims (uniformPopulation (Fin 5)) ∧
  IVConsistencyClaims upDownWitness ∧
  IVConsistencyClaims modelA ∧
  IVConsistencyClaims modelB ∧
  UpDownAverageClaims ∧
  eventProb (uniformPopulation (Fin 5)) (increaser modelA) = 2/5 ∧
  eventProb (uniformPopulation (Fin 5)) (increaser modelB) = 3/5 ∧
  increaserPerUnitEffect upDownPopulation upDownWitness = 1 ∧
  increaserPerUnitEffect (uniformPopulation (Fin 5)) modelA = 1 ∧
  increaserPerUnitEffect (uniformPopulation (Fin 5)) modelB = 4/3

end
end SAP.P043
