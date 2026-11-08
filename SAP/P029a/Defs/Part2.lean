import SAP.P029a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P029a

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

def weightWitnessAssignment (i : Bool × Bool × Fin 4) : Bool := i.2.1

def receiptDependentWeight (i : Bool × Bool × Fin 4) : ℝ :=
  if (weightWitnessResponse i).receivedTreatment (weightWitnessAssignment i) then 9 else 1

def specifiedUnweightedScores (x : Bool) : ℝ := if x then 3/4 else 1/4

def specifiedWeightedScores (x : Bool) : ℝ := if x then 27/28 else 3/4

def twoSidedSuccessCount (i : Bool × Bool) : ℕ := if i.2 then (if i.1 then 3 else 2) else 1

def specifiedInsideLogRates (i : Bool × Bool) : ℝ := if i.2 then (if i.1 then 3/4 else 1/2) else 1/4

def specifiedWeightedRates (i : Bool × Bool) : ℝ := if i.2 then (if i.1 then 27/28 else 9/10) else 3/4

def fourCellLikelihood (q : Bool × Bool → ℝ) : ℝ :=
  ∏ i, q i ^ twoSidedSuccessCount i * (1 - q i) ^ (4 - twoSidedSuccessCount i)

def codedBenchmark {n : ℕ} (x : Fin n → Fin 3 → ℝ) : ℝ :=
  (∑ i, 5 * (1 + x i 0 + x i 1 + x i 2)) / n

def uniformCovariateLaw : Measure ℝ :=
  ProbabilityTheory.cond volume (Ioo (-1 : ℝ) 1)

def observedNoiseProfile (k : Fin 5) : Fin 3 → ℝ :=
  if k.val = 0 then ![0,0,0] else
  if k.val = 1 then ![1/2,0,0] else
  if k.val = 2 then ![0,1/2,0] else
  if k.val = 3 then ![0,0,1/2] else ![-1/2,-1/2,-1/2]

abbrev NoiseRecord := Fin 50 × Fin 5 × Bool

def noiseDesignMatrix : Matrix NoiseRecord (Fin 5) ℝ :=
  fun i => ![1, indicatorValue i.2.2, observedNoiseProfile i.2.1 0, observedNoiseProfile i.2.1 1, observedNoiseProfile i.2.1 2]

def noiseGramMatrix : Matrix (Fin 5) (Fin 5) ℝ :=
  !![500,250,0,0,0; 250,250,0,0,0; 0,0,50,25,25; 0,0,25,50,25; 0,0,25,25,50]

def noisePotentialResponse (opposite : Bool) (i : NoiseRecord) : PotentialResponse (Fin 3 → ℝ) :=
  let y0 := 5 + (if opposite then indicatorValue i.2.2 else 0)
  ⟨observedNoiseProfile i.2.1, false, true, y0, y0+5⟩

def recordCellCount (k : Fin 9) : ℕ := ![602,768,2514,160,155,461,1789,5247,7237] k

abbrev CanvassingRecord : Type := Sigma (fun k : Fin 9 => Fin (recordCellCount k))

def recordedRace (i : CanvassingRecord) : Option Bool :=
  if i.1.val < 3 then some true else if i.1.val < 6 then some false else none

def recordedAssignment (i : CanvassingRecord) : Bool := decide (i.1.val % 3 < 2)

def recordedContact (i : CanvassingRecord) : Bool := decide (i.1.val % 3 = 0)

def raceCompletionA (i : CanvassingRecord) : Bool := decide (i.1.val < 3)

def raceCompletionB (i : CanvassingRecord) : Bool := decide (i.1.val < 3 ∨ 6 ≤ i.1.val)

def recordMass (_ : CanvassingRecord) : ℝ := 1/18933

def recordPotentialResponse (Y : CanvassingRecord → ℝ) (i : CanvassingRecord) : PotentialResponse Unit :=
  ⟨(), false, recordedContact i, Y i, Y i⟩

def PreservesRecordedRace (W : CanvassingRecord → Bool) : Prop :=
  ∀ i b, recordedRace i = some b → W i = b

def completedRawRaceRecord (R : CanvassingRecord → Option String)
    (W : CanvassingRecord → Bool) (i : CanvassingRecord) : Option String × Bool :=
  (R i, W i)

def trueCount {n : ℕ} (W : Fin n → Bool) : ℕ :=
  by
  classical
  exact (Finset.univ.filter (fun i => W i = true)).card

def jointTrueCount {n : ℕ} (C W : Fin n → Bool) : ℕ :=
  by
  classical
  exact (Finset.univ.filter (fun i => C i = true ∧ W i = true)).card

def finiteGroupMean {L G : Type*} [Fintype L] (p s : L → ℝ) (group : L → G) (g : G) : ℝ :=
  finiteConditionalMean p s (fun i => group i = g)

def semComplianceMass (t : Bool) : ℝ := if t then 1/4 else 3/4

def semDefierResponse (t : Bool) : PotentialResponse Unit :=
  ⟨(), t, !t, indicatorValue t - 1/4, indicatorValue t - 1/4 + 1⟩

def semDefierWitnessMass : Bool × Bool → ℝ := bernoulliProductMass semComplianceMass (1/4)

def semDefierResidual (i : Bool × Bool) : ℝ :=
  indicatorValue ((semDefierResponse i.1).receivedTreatment i.2) - 1/4 - indicatorValue i.2 / 2

def semDependentResponse (i : Fin 4) : PotentialResponse Unit :=
  let u : ℝ := ![-2,-1,1,2] i
  ⟨(), decide (0 < u), true, u, u + 1⟩

def semDependentAssignment (i : Fin 4) : Bool := decide (i.val = 0 ∨ i.val = 3)

def semDependentResidual (i : Fin 4) : ℝ :=
  indicatorValue ((semDependentResponse i).receivedTreatment (semDependentAssignment i)) - 1/2 - indicatorValue (semDependentAssignment i)/2

def heterogeneousResponse (h : Bool) : PotentialResponse Unit :=
  ⟨(), false, true, 0, if h then 2 else 1⟩

def closedReceiptTriangle : Set (ℝ × ℝ) := {v | 0 ≤ v.2 ∧ v.2 ≤ v.1 ∧ v.1 ≤ 1}

def positiveComplianceDifference (r1 r0 : ℝ) : ℝ := max (r1 - r0) 0

def twoReceiptFit (d : Bool × Bool) : ℝ × ℝ :=
  if d.1 then (if d.2 then (1,1) else (1,0))
  else (if d.2 then (1/2,1/2) else (0,0))

def twoReceiptMass (d : Bool × Bool) : ℝ :=
  (if d.1 then 3/4 else 1/4) * (if d.2 then 1/4 else 3/4)

def twoReceiptLikelihood (d : Bool × Bool) (p q : ℝ) : ℝ :=
  bernoulliContribution p d.1 * bernoulliContribution q d.2

def binomialCountMass (n : ℕ) (p : ℝ) (k : Fin (n+1)) : ℝ :=
  (n.choose k.val : ℝ) * p^k.val * (1-p)^(n-k.val)

def independentArmCountMass (n1 n0 : ℕ) (p1 p0 : ℝ) : Fin (n1+1) × Fin (n0+1) → ℝ :=
  fun k => binomialCountMass n1 p1 k.1 * binomialCountMass n0 p0 k.2

def empiricalPositiveScore (n1 n0 : ℕ) (k : Fin (n1+1) × Fin (n0+1)) : ℝ :=
  positiveComplianceDifference ((k.1.val : ℝ)/n1) ((k.2.val : ℝ)/n0)

def positiveIndexIndicator (index : ℝ) : ℝ := if 0 < index then 1 else 0

def latentAlwaysOrComplier (indexAC : ℝ) : ℝ := positiveIndexIndicator indexAC

def latentAlwaysTaker (indexAC indexA : ℝ) : ℝ := positiveIndexIndicator indexA * latentAlwaysOrComplier indexAC

def latentComplier (indexAC indexA : ℝ) : ℝ := latentAlwaysOrComplier indexAC - latentAlwaysTaker indexAC indexA

def latentReceipt (indexAC indexA : ℝ) (z : Bool) : ℝ :=
  latentComplier indexAC indexA * indicatorValue z + latentAlwaysTaker indexAC indexA

def perturbedRecordWeight (t : ℝ) (i : Bool × Bool × Fin 4) : ℝ :=
  if i.1 = false ∧ i.2.1 = true ∧ i.2.2.val = 1 then t else 1

def specifiedPerturbedScores (t : ℝ) (x : Bool) : ℝ := if x then 3/4 else 1/(3+t)

def IgnorabilityWitnessFacts : Prop :=
    FiniteIVConditions sixAtomMass (assignResponse ignorabilityResponse) Prod.snd ∧
    FiniteReceiptIgnorability sixAtomMass (assignResponse ignorabilityResponse) Prod.snd () ∧
    finiteProbability sixAtomMass (fun i => (ignorabilityResponse i.1).receivedTreatment i.2 = true) = 1/2 ∧
    finiteProbability sixAtomMass (fun i => (ignorabilityResponse i.1).receivedTreatment i.2 = false) = 1/2 ∧
    finiteConditionalMean sixAtomMass (fun i => if (ignorabilityResponse i.1).isComplier then 1 else 0)
      (fun i => (ignorabilityResponse i.1).receivedTreatment i.2 = true) = 1/2 ∧
    finiteConditionalMean sixAtomMass (fun i => if (ignorabilityResponse i.1).isComplier then 1 else 0)
      (fun i => (ignorabilityResponse i.1).receivedTreatment i.2 = false) = 1/2 ∧
    finiteExpectation sixAtomMass (fun i => (ignorabilityResponse i.1).treatmentEffect) = 1/2 ∧
    finiteConditionalMean sixAtomMass (fun i => (ignorabilityResponse i.1).treatmentEffect) (fun i => (ignorabilityResponse i.1).isComplier) = 1 ∧
    finiteComplianceScore sixAtomMass (assignResponse ignorabilityResponse) () = 1/2 ∧
    (1/4 : ℝ) < finiteComplianceScore sixAtomMass (assignResponse ignorabilityResponse) () ∧
    finiteWald sixAtomMass (assignResponse ignorabilityResponse) Prod.snd (fun _ => 1) = 1 ∧
    finiteWald sixAtomMass (assignResponse ignorabilityResponse) Prod.snd
      (fun i => 1 / finiteComplianceScore sixAtomMass (assignResponse ignorabilityResponse) (ignorabilityResponse i.1).x) = 1

def PotentialPairIndependence : Prop :=
    FiniteIndependent sixAtomMass (fun i => ((ignorabilityResponse i.1).y0, (ignorabilityResponse i.1).y1))
      (fun i => (ignorabilityResponse i.1).receivedTreatment i.2)

def OneSidedImplication : Prop :=
  ∀ {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialResponse X) (Z : Ω → Bool)
    (hiv : IVConditions μ U Z) (hside : ∀ᵐ ω ∂μ, (U ω).d0 = false)
    (x : X) (hx : 0 < eventProbability μ {ω | (U ω).x = x}) (hc : 0 < complianceProbability μ U x)
    (hi : ReceiptMeanEquality μ U Z x),
    LatentMeanEquality μ U x

def BaselineSelectionFacts : Prop :=
    FiniteIVConditions sixAtomMass (assignResponse baselineResponse) Prod.snd ∧
    FiniteLatentIgnorability sixAtomMass (assignResponse baselineResponse) ∧
    finiteConditionalMean sixAtomMass (fun i => (baselineResponse i.1).y0)
      (fun i => (baselineResponse i.1).receivedTreatment i.2 = true) = 1/2 ∧
    finiteConditionalMean sixAtomMass (fun i => (baselineResponse i.1).y0)
      (fun i => (baselineResponse i.1).receivedTreatment i.2 = false) = 0 ∧
    finiteConditionalMean sixAtomMass (fun i => (baselineResponse i.1).y1)
      (fun i => (baselineResponse i.1).receivedTreatment i.2 = true) = 3/2 ∧
    finiteConditionalMean sixAtomMass (fun i => (baselineResponse i.1).y1)
      (fun i => (baselineResponse i.1).receivedTreatment i.2 = false) = 1

def IgnorabilityIncomparability : Prop :=
    (FiniteIVConditions sixAtomMass (assignResponse ignorabilityResponse) Prod.snd ∧
      FiniteReceiptIgnorability sixAtomMass (assignResponse ignorabilityResponse) Prod.snd () ∧
      ¬ FiniteLatentIgnorability sixAtomMass (assignResponse ignorabilityResponse)) ∧
    (FiniteIVConditions sixAtomMass (assignResponse baselineResponse) Prod.snd ∧
      FiniteLatentIgnorability sixAtomMass (assignResponse baselineResponse) ∧
      ¬ FiniteReceiptIgnorability sixAtomMass (assignResponse baselineResponse) Prod.snd ())

end
end SAP.P029a
