import SAP.P037a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P037a

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

def compositionFinite : Prop :=
  (∀ w, 0 ≤ assignmentMass w) ∧ (∑ w, assignmentMass w) = 1 ∧
      (∀ i, compositionMean (fun w => treatment w.1 i) = 1/2 ∧
        2*compositionMean (fun w => compositionColumn w i) = eligibleFraction i ∧
        2*compositionMean (fun w =>
          (compositionColumn w i-treatment w.1 i*eligibleFraction i)^2) =
          eligibleFraction i*(1-eligibleFraction i)/36) ∧
      (∀ i k, k.val ≤ 4 → 0 < countMass (stratumReferents i) k) ∧
      (∀ i c c', potentialOutcome i true c-potentialOutcome i true c'=0) ∧
      (∀ c : ℝ, (∑ i : Fin 4,
        (potentialOutcome i true c-potentialOutcome i false c))/4 = -1/5) ∧
      (∀ theta : Fin 3 → ℝ, populationGram.mulVec theta = populationRhs ↔
        theta = ![-3/31,-15/62,-16/31]) ∧ (-16/31:ℝ) ≠ 0

def compositionExpectedMatrices : Prop :=
  populationGram = !![1,0,1/5; 0,1/25,1/50; 1/5,1/50,151/2400] ∧
      populationRhs = ![-1/5,-1/50,-17/300]

def compositionDeterminant : Prop := populationGram.det = 31/60000 ∧ populationGram.det ≠ 0

def compositionMixtureCurve : Prop :=
  ∀ (a tau b1 b2 g : ℝ),
    (∀ i c c', mixturePotential a tau b1 b2 g i true c-
        mixturePotential a tau b1 b2 g i true c'=b1*(c-c')) ∧
      (∀ c : ℝ, (∑ i : Fin 4,
        (mixturePotential a tau b1 b2 g i true c-
         mixturePotential a tau b1 b2 g i false c))/4=tau+b1*(c-1/5))

def compositionMixtureCoefficient : Prop :=
  ∀ (a tau b1 b2 g : ℝ),
    ∃ theta : Fin 3 → ℝ,
        (populationGram.mulVec theta = fun k => compositionMean (fun w =>
          centeredCross (regressionColumns w k) (mixtureObserved a tau b1 b2 g w))) ∧
        (∀ theta' : Fin 3 → ℝ,
          (populationGram.mulVec theta' = fun k => compositionMean (fun w =>
            centeredCross (regressionColumns w k) (mixtureObserved a tau b1 b2 g w))) →
          theta' = theta) ∧
        theta 2 = (15*b1+16*b2)/31 ∧ (theta 2 = b1 ↔ b1=b2)

def compositionWitnessParameters : Prop :=
  (∀ w i, mixtureObserved (3/10) (-1/5) 0 (-1) 0 w i = observedOutcome w i) ∧
  (∀ i treated c, mixturePotential (3/10) (-1/5) 0 (-1) 0 i treated c =
    potentialOutcome i treated c)

def T1Statement : Prop :=
  compositionFinite ∧ compositionExpectedMatrices ∧ compositionDeterminant ∧
  compositionMixtureCurve ∧ compositionMixtureCoefficient ∧ compositionWitnessParameters

end SAP.P037a
