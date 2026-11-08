import SAP.P043.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P043

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
universe u v

/-! The substantive numerical, response, and distributional claims for both mediation counterexamples. -/

def LinearNumericClaims : Prop :=
  contrast linearPopulation (1/2) linearWitness.knowledge = 6/5 ∧
  mediated linearPopulation linearWitness = 3/50 ∧
  direct linearPopulation linearWitness = -3/50 ∧
  reducedForm linearPopulation (1/2) linearWitness = 0 ∧
  variance linearPopulation (1/2) (fun t _ => assignment t) = 1/4 ∧
  covariance linearPopulation (1/2) (fun t _ => assignment t)
    (observedSupport linearWitness) = 0 ∧
  covariance linearPopulation (1/2) (fun t _ => assignment t) linearWitness.knowledge = 3/10 ∧
  assignmentSlope linearPopulation (1/2) (observedSupport linearWitness) = 0 ∧
  assignmentSlope linearPopulation (1/2) linearWitness.knowledge = 6/5 ∧
  (6/5 : ℝ) * (1/20) = 3/50 ∧ (6/5 : ℝ) * (1/20) + (-3/50) = 0

def LinearWitnessClaims : Prop :=
    (∀ t i, jointMass linearPopulation (1/2) t i = 1/8) ∧
    (∀ r s : Bool, eventProb linearPopulation (fun i => i.1 = r ∧ i.2 = s) = 1/4) ∧
    (∀ r : Bool, eventProb linearPopulation (fun i => i.1 = r) = 1/2 ∧
      eventProb linearPopulation (fun i => i.2 = r) = 1/2) ∧
    (∀ i, linearWitness.knowledge true i - linearWitness.knowledge false i = 6/5 ∧
      0 < linearWitness.knowledge true i - linearWitness.knowledge false i) ∧
    (∀ t k h i, 0 < h → linearWitness.support t (k+h) i - linearWitness.support t k i = h/20 ∧
      0 < linearWitness.support t (k+h) i - linearWitness.support t k i) ∧
    LinearNumericClaims ∧
    (∀ t y, armMean linearPopulation (1/2) t
      (fun z i => indicator (observedSupport linearWitness z i = y)) =
      if y = 219/100 ∨ y = 221/100 ∨ y = 239/100 ∨ y = 241/100 then 1/4 else 0) ∧
    reducedForm linearPopulation (1/2) linearWitness < mediated linearPopulation linearWitness ∧
    0 < mediated linearPopulation linearWitness

def IntegerNumericClaims : Prop :=
  armMean integerPopulation (1/2) false integerWitness.knowledge = 8 ∧
  armMean integerPopulation (1/2) true integerWitness.knowledge = 46/5 ∧
  mean integerPopulation (fun i => integerWitness.knowledge true i - integerWitness.knowledge false i) = 6/5 ∧
  mean integerPopulation (fun i => integerWitness.support false (integerWitness.knowledge false i) i) = 59/25 ∧
  mean integerPopulation (fun i => integerWitness.support false (integerWitness.knowledge true i) i) = 121/50 ∧
  mean integerPopulation (fun i => integerWitness.support true (integerWitness.knowledge true i) i) = 59/25 ∧
  mediated integerPopulation integerWitness = 3/50 ∧
  direct integerPopulation integerWitness = -3/50 ∧
  reducedForm integerPopulation (1/2) integerWitness = 0

def IntegerWitnessClaims : Prop :=
    (∀ t i, jointMass integerPopulation (1/2) t i = 1/1000) ∧
    (∀ t i, integerWitness.knowledge t i ∈ ({8,9,10} : Finset ℝ) ∧
      observedSupport integerWitness t i ∈ ({2,3} : Finset ℝ) ∧
      integerGeneralKnowledge t i = 2) ∧
    (∀ t k, k=8 ∨ k=9 →
      (∀ i, integerWitness.support t (k+1) i - integerWitness.support t k i ∈ ({0,1} : Finset ℝ)) ∧
      mean integerPopulation (fun i => integerWitness.support t (k+1) i - integerWitness.support t k i) = 1/20) ∧
    IntegerNumericClaims ∧
    (∀ t y, armMean integerPopulation (1/2) t
      (fun z i => indicator (observedSupport integerWitness z i = y)) =
      if y=2 then 16/25 else if y=3 then 9/25 else 0) ∧
    reducedForm integerPopulation (1/2) integerWitness < mediated integerPopulation integerWitness ∧
    0 < mediated integerPopulation integerWitness

/-- Both mediation witnesses, including independent assignment for every population event.
The exact finite support sets encode the corresponding index bounds. -/
def T1Statement : Prop :=
  LinearWitnessClaims ∧ IntegerWitnessClaims ∧
  reducedForm linearPopulation (1/2) linearWitness = 0 ∧
  mediated linearPopulation linearWitness = 3/50 ∧
  direct linearPopulation linearWitness = -3/50 ∧
  reducedForm integerPopulation (1/2) integerWitness = 0 ∧
  mediated integerPopulation integerWitness = 3/50 ∧
  direct integerPopulation integerWitness = -3/50 ∧
  (∀ A t, (∑ i, jointMass linearPopulation (1/2) t i * indicator (A i)) =
    armProb (1/2) t * eventProb linearPopulation A) ∧
  (∀ A t, (∑ i, jointMass integerPopulation (1/2) t i * indicator (A i)) =
    armProb (1/2) t * eventProb integerPopulation A)

end
end SAP.P043
