import SAP.P029a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029a

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

noncomputable section

/-- The project's parametric RMSE formula, with a positive run size required in the claim. -/
def rootMeanSquaredError {R : ℕ} (t benchmark : Fin R → ℝ) : ℝ :=
  Real.sqrt ((∑ r, (t r - benchmark r)^2) / R)

/-- Count-weighted distribution of the nine recorded demographic cells. -/
def recordCellMass (k : Fin 9) : ℝ := (recordCellCount k : ℝ) / 18933

/-- Difference between the normalized, weighted means of the two assignment arms. -/
def finiteArmDifference {L : Type*} [Fintype L]
    (p : L → ℝ) (Z : L → Bool) (w v : L → ℝ) : ℝ :=
  finiteConditionalMean p (fun i => w i * v i) (fun i => Z i = true) /
      finiteConditionalMean p w (fun i => Z i = true) -
    finiteConditionalMean p (fun i => w i * v i) (fun i => Z i = false) /
      finiteConditionalMean p w (fun i => Z i = false)

/-- The additional explicit conditional means in the six-atom counterexample. -/
def IgnorabilityWitnessMeans : Prop :=
  finiteProbability sixAtomMass (fun i => i.2 = true) = 1/2 ∧
  finiteConditionalMean sixAtomMass (fun i => indicatorValue ((ignorabilityResponse i.1).receivedTreatment i.2))
    (fun i => i.2 = true) = 3/4 ∧
  finiteConditionalMean sixAtomMass (fun i => indicatorValue ((ignorabilityResponse i.1).receivedTreatment i.2))
    (fun i => i.2 = false) = 1/4 ∧
  (∀ z, finiteConditionalMean sixAtomMass (fun i => (ignorabilityResponse i.1).y1)
    (fun i => (ignorabilityResponse i.1).receivedTreatment i.2 = z) = 1/2) ∧
  (∀ z, finiteConditionalMean sixAtomMass (fun i => (ignorabilityResponse i.1).y0)
    (fun i => (ignorabilityResponse i.1).receivedTreatment i.2 = z) = 0) ∧
  finiteConditionalMean sixAtomMass (fun i => (ignorabilityResponse i.1).observedOutcome i.2)
    (fun i => i.2 = true) = 1/2 ∧
  finiteConditionalMean sixAtomMass (fun i => (ignorabilityResponse i.1).observedOutcome i.2)
    (fun i => i.2 = false) = 0 ∧
  (∀ i : Fin 3 × Bool, 1 / finiteComplianceScore sixAtomMass (assignResponse ignorabilityResponse)
    (ignorabilityResponse i.1).x = 2) ∧
  ¬ FiniteLatentIgnorability sixAtomMass (assignResponse ignorabilityResponse)

def BaselineEffectFacts : Prop :=
  (∀ i, (baselineResponse i).treatmentEffect = 1) ∧
  finiteExpectation sixAtomMass (fun i => (baselineResponse i.1).treatmentEffect) = 1 ∧
  finiteConditionalMean sixAtomMass (fun i => (baselineResponse i.1).treatmentEffect)
    (fun i => (baselineResponse i.1).isComplier) = 1

/-- Additional exact values of the two binary-covariate witnesses. -/
def IndependenceWitnessMeans : Prop :=
  finiteProbability marginalWitnessMass (fun i => (binaryEffectResponse i.1).isComplier) = 1/2 ∧
  finiteConditionalMean marginalWitnessMass (fun i => (binaryEffectResponse i.1).treatmentEffect)
    (fun i => (binaryEffectResponse i.1).isComplier) = 1/2 ∧
  finiteExpectation marginalWitnessMass (fun i => if (binaryEffectResponse i.1).isComplier
    then (binaryEffectResponse i.1).treatmentEffect else 0) = 1/4 ∧
  finiteArmDifference marginalWitnessMass Prod.snd
    (fun i => 1 / finiteComplianceScore marginalWitnessMass (assignResponse binaryEffectResponse)
      (binaryEffectResponse i.1).x)
    (fun i => (binaryEffectResponse i.1).observedOutcome i.2) = 7/34 ∧
  finiteArmDifference marginalWitnessMass Prod.snd
    (fun i => 1 / finiteComplianceScore marginalWitnessMass (assignResponse binaryEffectResponse)
      (binaryEffectResponse i.1).x)
    (fun i => indicatorValue ((binaryEffectResponse i.1).receivedTreatment i.2)) = 8/17 ∧
  (∀ x, finiteProbability conditionalWitnessMass (fun i => (binaryEffectResponse i.1).x = x) = 1/2) ∧
  finiteProbability conditionalWitnessMass (fun i => (binaryEffectResponse i.1).isComplier) = 1/2 ∧
  finiteConditionalMean conditionalWitnessMass (fun i => (binaryEffectResponse i.1).treatmentEffect)
    (fun i => (binaryEffectResponse i.1).isComplier) = 5/8 ∧
  finiteArmDifference conditionalWitnessMass Prod.snd
    (fun i => 1 / finiteComplianceScore conditionalWitnessMass (assignResponse binaryEffectResponse)
      (binaryEffectResponse i.1).x)
    (fun i => (binaryEffectResponse i.1).observedOutcome i.2) = 3/16 ∧
  finiteArmDifference conditionalWitnessMass Prod.snd
    (fun i => 1 / finiteComplianceScore conditionalWitnessMass (assignResponse binaryEffectResponse)
      (binaryEffectResponse i.1).x)
    (fun i => indicatorValue ((binaryEffectResponse i.1).receivedTreatment i.2)) = 3/8

def IndependenceWitnessNumbers : Prop :=
  (∀ c t : Bool, finiteProbability marginalWitnessMass
    (fun i => i.1.1.1 = c ∧ i.1.1.2.1 = t) = 1/4) ∧
  (∀ x : Bool, 1 / finiteComplianceScore marginalWitnessMass (assignResponse binaryEffectResponse) x =
    if x then 3/2 else 5/2) ∧
  (∀ x : Bool, 1 / finiteComplianceScore conditionalWitnessMass (assignResponse binaryEffectResponse) x =
    if x then 4/3 else 4) ∧
  finiteProbability conditionalWitnessMass (fun i => i.1.1.2.1 = true) = 1/2 ∧
  finiteProbability conditionalWitnessMass (fun i => i.1.1.2.1 = false) = 1/2 ∧
  finiteArmDifference marginalWitnessMass Prod.snd (fun _ => 1)
    (fun i => (binaryEffectResponse i.1).observedOutcome i.2) = 1/4 ∧
  finiteArmDifference marginalWitnessMass Prod.snd (fun _ => 1)
    (fun i => indicatorValue ((binaryEffectResponse i.1).receivedTreatment i.2)) = 1/2 ∧
  ((5/8 : ℝ)*(1/4) + (3/8)*(3/4) = 7/16)

/-- The actual outcome cross-products and coefficient vectors for both noise inputs. -/
def NoiseCrossProductFacts : Prop :=
  noiseDesignMatrix.transpose.mulVec (fun i => 5 + 5 * indicatorValue i.2.2) = ![3750,2500,0,0,0] ∧
  noiseDesignMatrix.transpose.mulVec (fun i => 5 + 6 * indicatorValue i.2.2) = ![4000,2750,0,0,0] ∧
  noiseGramMatrix⁻¹.mulVec
    (noiseDesignMatrix.transpose.mulVec (fun i => 5 + 5 * indicatorValue i.2.2)) = ![5,5,0,0,0] ∧
  noiseGramMatrix⁻¹.mulVec
    (noiseDesignMatrix.transpose.mulVec (fun i => 5 + 6 * indicatorValue i.2.2)) = ![5,6,0,0,0]

/-- The corrected statistic is defined only for a positive number of replicates. -/
def CorrectedRMSE : Prop :=
  ∀ (R : ℕ), 0 < R → ∀ t : Fin R → ℝ,
    rootMeanSquaredError t (fun _ => 5) = Real.sqrt ((∑ r, (t r - 5)^2) / R)

/-- Repeating either admissible input gives opposite RMSE discrepancies for any nonempty run. -/
def ConstantRunScoringFacts : Prop :=
  ∀ (R : ℕ), 0 < R →
    rootMeanSquaredError (fun _ : Fin R => 5) (fun _ => 6) = 1 ∧
    rootMeanSquaredError (fun _ : Fin R => 5) (fun _ => 5) = 0 ∧
    rootMeanSquaredError (fun _ : Fin R => 6) (fun _ => 6) = 0 ∧
    rootMeanSquaredError (fun _ : Fin R => 6) (fun _ => 5) = 1

/-- A saturated Bernoulli model with a free probability for each named cell. -/
def IsUniqueFreeCellFit {I C : Type*} [Fintype I]
    (cell : I → C) (D : I → Bool) (w : I → ℝ) (qhat : C → ℝ) : Prop :=
  (∀ c, qhat c ∈ Ioo (0 : ℝ) 1) ∧
  ∀ q : C → ℝ, (∀ c, q c ∈ Ioo (0 : ℝ) 1) →
    observationWeightedObjective (fun i => bernoulliContribution (qhat (cell i)) (D i)) w ≤
      observationWeightedObjective (fun i => bernoulliContribution (q (cell i)) (D i)) w ∧
    (observationWeightedObjective (fun i => bernoulliContribution (qhat (cell i)) (D i)) w =
      observationWeightedObjective (fun i => bernoulliContribution (q (cell i)) (D i)) w ↔ q = qhat)

def treatedReceipt (i : Bool × Fin 4) : Bool :=
  (weightWitnessResponse (i.1,true,i.2)).receivedTreatment true

def treatedWeight (i : Bool × Fin 4) : ℝ := receiptDependentWeight (i.1,true,i.2)

def treatedPerturbationWeight (t : ℝ) (i : Bool × Fin 4) : ℝ :=
  perturbedRecordWeight t (i.1,true,i.2)

def twoSidedReceipt (i : (Bool × Bool) × Fin 4) : Bool :=
  decide (i.2.val < twoSidedSuccessCount i.1)

def twoSidedObservationWeight (i : (Bool × Bool) × Fin 4) : ℝ :=
  if twoSidedReceipt i then 9 else 1

/-- Concrete fitting certificates concern free probabilities, with no coefficient parametrization. -/
def ConcreteFreeCellFits : Prop :=
  IsUniqueFreeCellFit Prod.fst treatedReceipt treatedWeight specifiedWeightedScores ∧
  (∀ t : ℝ, 0 < t → IsUniqueFreeCellFit Prod.fst treatedReceipt
    (treatedPerturbationWeight t) (specifiedPerturbedScores t)) ∧
  IsUniqueFreeCellFit Prod.fst twoSidedReceipt twoSidedObservationWeight specifiedWeightedRates

end
end SAP.P029a
