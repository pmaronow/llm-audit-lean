import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P029a

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

def indicatorValue (b : Bool) : ℝ := if b then 1 else 0

structure PotentialResponse (X : Type*) where
  x : X
  d0 : Bool
  d1 : Bool
  y0 : ℝ
  y1 : ℝ

def PotentialResponse.treatmentEffect {X : Type*} (u : PotentialResponse X) : ℝ := u.y1 - u.y0

def PotentialResponse.isComplier {X : Type*} (u : PotentialResponse X) : Prop :=
  u.d0 = false ∧ u.d1 = true

def PotentialResponse.isDefier {X : Type*} (u : PotentialResponse X) : Prop :=
  u.d0 = true ∧ u.d1 = false

def PotentialResponse.receivedTreatment {X : Type*} (u : PotentialResponse X) (z : Bool) : Bool :=
  if z then u.d1 else u.d0

def PotentialResponse.observedOutcome {X : Type*} (u : PotentialResponse X) (z : Bool) : ℝ :=
  if u.receivedTreatment z then u.y1 else u.y0

def IsFiniteLaw {L : Type*} [Fintype L] (p : L → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1

def finiteExpectation {L : Type*} [Fintype L] (p v : L → ℝ) : ℝ := ∑ i, p i * v i

def finiteProbability {L : Type*} [Fintype L] (p : L → ℝ) (A : L → Prop) : ℝ :=
  ∑ i, if A i then p i else 0

def finiteConditionalMean {L : Type*} [Fintype L] (p v : L → ℝ) (A : L → Prop) : ℝ :=
  finiteExpectation p (fun i => if A i then v i else 0) / finiteProbability p A

def finiteCovariance {L : Type*} [Fintype L] (p u v : L → ℝ) : ℝ :=
  finiteExpectation p (fun i => u i * v i) - finiteExpectation p u * finiteExpectation p v

def finiteVariance {L : Type*} [Fintype L] (p v : L → ℝ) : ℝ := finiteCovariance p v v

def finiteCorrelation {L : Type*} [Fintype L] (p u v : L → ℝ) : ℝ :=
  finiteCovariance p u v / Real.sqrt (finiteVariance p u * finiteVariance p v)

def FiniteIndependent {L A B : Type*} [Fintype L] (p : L → ℝ) (U : L → A) (V : L → B) : Prop :=
  ∀ a b, finiteProbability p (fun i => U i = a ∧ V i = b) =
    finiteProbability p (fun i => U i = a) * finiteProbability p (fun i => V i = b)

def bernoulliProductMass {L : Type*} (p : L → ℝ) (e : ℝ) : L × Bool → ℝ :=
  fun i => p i.1 * if i.2 then e else 1 - e

def finiteWald {L X : Type*} [Fintype L] (p : L → ℝ) (U : L → PotentialResponse X)
    (Z : L → Bool) (w : L → ℝ) : ℝ :=
  ((finiteConditionalMean p (fun i => w i * (U i).observedOutcome (Z i)) (fun i => Z i = true) /
      finiteConditionalMean p w (fun i => Z i = true)) -
    (finiteConditionalMean p (fun i => w i * (U i).observedOutcome (Z i)) (fun i => Z i = false) /
      finiteConditionalMean p w (fun i => Z i = false))) /
  ((finiteConditionalMean p (fun i => w i * indicatorValue ((U i).receivedTreatment (Z i))) (fun i => Z i = true) /
      finiteConditionalMean p w (fun i => Z i = true)) -
    (finiteConditionalMean p (fun i => w i * indicatorValue ((U i).receivedTreatment (Z i))) (fun i => Z i = false) /
      finiteConditionalMean p w (fun i => Z i = false)))

def finiteComplianceScore {L X : Type*} [Fintype L] (p : L → ℝ) (U : L → PotentialResponse X)
    (x : X) : ℝ := finiteProbability p (fun i => (U i).isComplier ∧ (U i).x = x) /
      finiteProbability p (fun i => (U i).x = x)

def FiniteLatentIgnorability {L X : Type*} [Fintype L] (p : L → ℝ)
    (U : L → PotentialResponse X) : Prop :=
  ∀ x, 0 < finiteProbability p (fun i => (U i).x = x) →
    finiteConditionalMean p (fun i => (U i).treatmentEffect) (fun i => (U i).x = x) =
    finiteConditionalMean p (fun i => (U i).treatmentEffect) (fun i => (U i).isComplier ∧ (U i).x = x)

def FiniteReceiptIgnorability {L X : Type*} [Fintype L] (p : L → ℝ)
    (U : L → PotentialResponse X) (Z : L → Bool) (x : X) : Prop :=
  finiteConditionalMean p (fun i => (U i).y0) (fun i => (U i).receivedTreatment (Z i) = true ∧ (U i).x = x) =
    finiteConditionalMean p (fun i => (U i).y0) (fun i => (U i).receivedTreatment (Z i) = false ∧ (U i).x = x) ∧
  finiteConditionalMean p (fun i => (U i).y1) (fun i => (U i).receivedTreatment (Z i) = true ∧ (U i).x = x) =
    finiteConditionalMean p (fun i => (U i).y1) (fun i => (U i).receivedTreatment (Z i) = false ∧ (U i).x = x)

def FiniteIVConditions {L X : Type*} [Fintype L] (p : L → ℝ) (U : L → PotentialResponse X)
    (Z : L → Bool) : Prop :=
  IsFiniteLaw p ∧ 0 < finiteProbability p (fun i => Z i = true) ∧ finiteProbability p (fun i => Z i = true) < 1 ∧
  FiniteIndependent p (fun i => ((U i).x, (U i).d0, (U i).d1, (U i).y0, (U i).y1)) Z ∧
  finiteProbability p (fun i => (U i).isDefier) = 0 ∧
  finiteConditionalMean p (fun i => indicatorValue ((U i).receivedTreatment (Z i))) (fun i => Z i = true) -
    finiteConditionalMean p (fun i => indicatorValue ((U i).receivedTreatment (Z i))) (fun i => Z i = false) ≠ 0

def complianceTypeMass (i : Fin 3) : ℝ := if i.val = 0 then 1/2 else 1/4

def ignorabilityResponse (i : Fin 3) : PotentialResponse Unit :=
  ⟨(), decide (i.val = 1), decide (i.val ≠ 2), 0, if i.val = 0 then 1 else 0⟩

def baselineResponse (i : Fin 3) : PotentialResponse Unit :=
  ⟨(), decide (i.val = 1), decide (i.val ≠ 2),
    if i.val = 1 then 1 else 0, (if i.val = 1 then 1 else 0) + 1⟩

def constantResponse (i : Fin 3) : PotentialResponse Unit :=
  ⟨(), decide (i.val = 1), decide (i.val ≠ 2), 0, 1⟩

def sixAtomMass : Fin 3 × Bool → ℝ := bernoulliProductMass complianceTypeMass (1/2)

def assignResponse {L X : Type*} (u : L → PotentialResponse X) : L × Bool → PotentialResponse X :=
  fun i => u i.1

abbrev BinaryTriple := Bool × Bool × Bool

def marginalBaseMass (i : BinaryTriple) : ℝ :=
  if i.1 ∧ i.2.1 then (if i.2.2 then 3/16 else 1/16)
  else (if i.2.2 then 1/16 else 3/16)

def conditionalBaseMass (i : BinaryTriple) : ℝ :=
  if i.1 = i.2.1 then
    (if i.1 = i.2.2 then 9/32 else 1/32)
  else 3/32

def binaryEffectResponse (i : BinaryTriple × Bool) : PotentialResponse Bool :=
  ⟨i.1.2.2, (!i.1.1) && i.2, ((!i.1.1) && i.2) || i.1.1, 0, indicatorValue i.1.2.1⟩

def marginalWitnessMass : (BinaryTriple × Bool) × Bool → ℝ :=
  bernoulliProductMass (bernoulliProductMass marginalBaseMass (1/2)) (1/2)

def conditionalWitnessMass : (BinaryTriple × Bool) × Bool → ℝ :=
  bernoulliProductMass (bernoulliProductMass conditionalBaseMass (1/2)) (1/2)

def FiniteConditionallyIndependent {L A B X : Type*} [Fintype L] (p : L → ℝ)
    (V : L → A) (W : L → B) (T : L → X) : Prop :=
  ∀ x a b, 0 < finiteProbability p (fun i => T i = x) →
    finiteProbability p (fun i => V i = a ∧ W i = b ∧ T i = x) / finiteProbability p (fun i => T i = x) =
    (finiteProbability p (fun i => V i = a ∧ T i = x) / finiteProbability p (fun i => T i = x)) *
    (finiteProbability p (fun i => W i = b ∧ T i = x) / finiteProbability p (fun i => T i = x))

def eventProbability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) : ℝ :=
  (μ A).toReal

def eventMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → ℝ)
    (A : Set Ω) : ℝ := (∫ ω in A, v ω ∂μ) / eventProbability μ A

def IVConditions {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialResponse X) (Z : Ω → Bool) : Prop :=
  Measurable (fun ω => (U ω).x) ∧ Measurable (fun ω => (U ω).d0) ∧
  Measurable (fun ω => (U ω).d1) ∧ Measurable (fun ω => (U ω).y0) ∧
  Measurable (fun ω => (U ω).y1) ∧ Measurable Z ∧
  Integrable (fun ω => (U ω).y0) μ ∧ Integrable (fun ω => (U ω).y1) μ ∧
  IndepFun Z (fun ω => ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1)) μ ∧
  0 < eventProbability μ {ω | Z ω = true} ∧ eventProbability μ {ω | Z ω = true} < 1 ∧
  μ {ω | (U ω).isDefier} = 0 ∧
  eventMean μ (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω))) {ω | Z ω = true} -
    eventMean μ (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω))) {ω | Z ω = false} ≠ 0

def LatentMeanEquality {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialResponse X) (x : X) : Prop :=
  eventMean μ (fun ω => (U ω).treatmentEffect) {ω | (U ω).x = x} =
    eventMean μ (fun ω => (U ω).treatmentEffect) {ω | (U ω).isComplier ∧ (U ω).x = x}

def ReceiptMeanEquality {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialResponse X) (Z : Ω → Bool) (x : X) : Prop :=
  eventMean μ (fun ω => (U ω).y0) {ω | (U ω).receivedTreatment (Z ω) = true ∧ (U ω).x = x} =
    eventMean μ (fun ω => (U ω).y0) {ω | (U ω).receivedTreatment (Z ω) = false ∧ (U ω).x = x} ∧
  eventMean μ (fun ω => (U ω).y1) {ω | (U ω).receivedTreatment (Z ω) = true ∧ (U ω).x = x} =
    eventMean μ (fun ω => (U ω).y1) {ω | (U ω).receivedTreatment (Z ω) = false ∧ (U ω).x = x}

def complianceProbability {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialResponse X) (x : X) : ℝ :=
  eventProbability μ {ω | (U ω).isComplier ∧ (U ω).x = x} / eventProbability μ {ω | (U ω).x = x}

def complierMeanEffect {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialResponse X) (x : X) : ℝ :=
  eventMean μ (fun ω => (U ω).treatmentEffect) {ω | (U ω).isComplier ∧ (U ω).x = x}

def weightedArmMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → Bool)
    (w v : Ω → ℝ) (z : Bool) : ℝ :=
  eventMean μ (fun ω => w ω * v ω) {ω | Z ω = z} / eventMean μ w {ω | Z ω = z}

def populationWald {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialResponse X) (Z : Ω → Bool) (w : Ω → ℝ) : ℝ :=
  (weightedArmMean μ Z w (fun ω => (U ω).observedOutcome (Z ω)) true -
    weightedArmMean μ Z w (fun ω => (U ω).observedOutcome (Z ω)) false) /
  (weightedArmMean μ Z w (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω))) true -
    weightedArmMean μ Z w (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω))) false)

def populationCovariance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (u v : Ω → ℝ) : ℝ :=
  (∫ ω, u ω * v ω ∂μ) - (∫ ω, u ω ∂μ) * (∫ ω, v ω ∂μ)

def bernoulliContribution (p : ℝ) (d : Bool) : ℝ :=
  p ^ (if d then 1 else 0 : ℕ) * (1 - p) ^ (if d then 0 else 1 : ℕ)

def nestedReceiptProbability (a b : ℝ) (z : Bool) : ℝ := a * (1 - b) * indicatorValue z + a * b

def insideLogObjective {I : Type*} [Fintype I] (L w : I → ℝ) : ℝ :=
  -(∑ i, Real.log (L i * w i))

def observationWeightedObjective {I : Type*} [Fintype I] (L w : I → ℝ) : ℝ :=
  -(∑ i, w i * Real.log (L i))

def IsGlobalMinimum {Θ : Type*} (Q : Θ → ℝ) (θ : Θ) : Prop := ∀ t, Q θ ≤ Q t

def extendedNegativeLog (x : ℝ) : EReal := if x = 0 then ⊤ else (-Real.log x : ℝ)

def extendedInsideLogObjective {I : Type*} [Fintype I] (L w : I → ℝ) : EReal :=
  ∑ i, extendedNegativeLog (L i*w i)

def cellLogLikelihood (S F q : ℝ) : ℝ := S * Real.log q + F * Real.log (1 - q)

def successWeightTotal {I C : Type*} [Fintype I] (cell : I → C) (D : I → Bool)
    (w : I → ℝ) (c : C) : ℝ := ∑ i, if cell i = c ∧ D i = true then w i else 0

def failureWeightTotal {I C : Type*} [Fintype I] (cell : I → C) (D : I → Bool)
    (w : I → ℝ) (c : C) : ℝ := ∑ i, if cell i = c ∧ D i = false then w i else 0

def weightWitnessResponse (i : Bool × Bool × Fin 4) : PotentialResponse Bool :=
  ⟨i.1, false, decide (i.2.2.val < if i.1 then 3 else 1), 0, 1 + indicatorValue i.1⟩

end
end SAP.P029a
