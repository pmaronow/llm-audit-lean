import Mathlib
import SAP.P015b.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P015b

universe u v

noncomputable section
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal NNReal
attribute [local instance] Classical.propDecidable

def profileLaw {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B) (x : B) : Measure Ω :=
  (P {s | X s = x})⁻¹ • P.restrict {s | X s = x}

def profileMean {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) (x : B) : ℝ := ∫ s, D s ∂profileLaw P X x

def profileVariance {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) (x : B) : ℝ := ∫ s, (D s-profileMean P X D x)^2 ∂profileLaw P X x

def profileProbability {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) (x : B) (d : ℝ) : ℝ := (profileLaw P X x {s | D s = d}).toReal

def profileWeight {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) (s : Ω) : ℝ := (D s-profileMean P X D (X s))^2

def effectiveProfileLaw {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) : Measure Ω :=
  (ENNReal.ofReal (∫ s, profileWeight P X D s ∂P))⁻¹ •
    P.withDensity (fun s => ENNReal.ofReal (profileWeight P X D s))

def smallWeightPopulation (ε : ℝ) : Fin 4 → ℝ := ![(1-ε)/2, ε/2, 1/4, 1/4]

def smallWeightOutcome (a : Fin 4) (d : ℝ) : ℝ := 2 * binaryProfile a + (1 + binaryProfile a) * d

def inverseWeightedOutcome {A : Type*} (D Y e : A → ℝ) : A → ℝ :=
  fun a => D a * Y a / e a - (1 - D a) * Y a / (1 - e a)

noncomputable def smallWeightIPW (ε : ℝ) : Fin 4 → ℝ :=
  inverseWeightedOutcome binaryTreatment (fun a => smallWeightOutcome a (binaryTreatment a))
    (fun a => ε + (1/2 - ε) * binaryProfile a)

def productMass {A : Type*} [Fintype A] (p : A → ℝ) (n : ℕ) : (Fin n → A) → ℝ :=
  fun a => ∏ i, p (a i)

def sampleMean {A : Type*} (Z : A → ℝ) (n : ℕ) (a : Fin n → A) : ℝ :=
  (∑ i, Z (a i))/(n : ℝ)

def uniformFourPopulation : Fin 4 → ℝ := ![1/4,1/4,1/4,1/4]

def zeroWeightControlDesign : Matrix (Fin 4) (Fin 2) ℝ := !![1,0; 1,0; 1,1; 1,1]

def zeroWeightRegressionDesign : Matrix (Fin 4) (Fin 3) ℝ := !![1,0,0; 1,0,0; 1,0,1; 1,1,1]

def zeroWeightTreatment : Fin 4 → ℝ := ![0,0,0,1]

def FittedZeroFailure : Prop :=
  (IsFiniteLaw uniformFourPopulation ∧
    (∀ x ∈ ({0,1} : Finset ℝ), ∀ d ∈ ({0,1} : Finset ℝ),
      finiteCellProbability uniformFourPopulation binaryProfile binaryTreatment x d = 1/2) ∧
    (∀ x ∈ ({0,1} : Finset ℝ),
      finiteCellMean uniformFourPopulation binaryProfile (finiteWeight uniformFourPopulation binaryProfile binaryTreatment) x = 1/4) ∧
    (1/4 : ℝ)^4 = 1/256 ∧ (0 : ℝ)  <  1/256 ∧
    zeroWeightControlDesign.transpose * zeroWeightControlDesign = !![4,2;2,2] ∧
    zeroWeightControlDesign.transpose.mulVec zeroWeightTreatment = ![1,1] ∧
    (!![4,2;2,2] : Matrix (Fin 2) (Fin 2) ℝ).mulVec ![0,1/2] = ![1,1] ∧
    (zeroWeightControlDesign.transpose * zeroWeightControlDesign).det ≠ 0 ∧
    treatmentResidual zeroWeightControlDesign zeroWeightTreatment ![0,1/2] = ![0,0,-1/2,1/2] ∧
    (fun a => treatmentResidual zeroWeightControlDesign zeroWeightTreatment ![0,1/2] a ^ 2) = ![0,0,1/4,1/4] ∧
    zeroWeightRegressionDesign.transpose * zeroWeightRegressionDesign = !![4,1,2;1,1,1;2,1,2] ∧
    (zeroWeightRegressionDesign.transpose * zeroWeightRegressionDesign).det = 2) ∧
  (sampleCoefficients zeroWeightControlDesign zeroWeightTreatment=![0,1/2] ∧
    treatmentResidual zeroWeightControlDesign zeroWeightTreatment (sampleCoefficients zeroWeightControlDesign zeroWeightTreatment)=![0,0,-1/2,1/2] ∧
    productMass uniformFourPopulation 4 (![0,0,2,3] : Fin 4 → Fin 4)=1/256) ∧
  (∀ i : Fin 4, zeroWeightControlDesign i 1=binaryProfile ((![0,0,2,3] : Fin 4 → Fin 4) i) ∧
      zeroWeightTreatment i=binaryTreatment ((![0,0,2,3] : Fin 4 → Fin 4) i))

/-- The positive implication in the passage, on the exported discrete finite-moment domain. -/
def DiscretePositivityImplications : Prop :=
  ∀ {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] [Countable B] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (D : Ω → ℝ) (_hX : Measurable X) (_hD : Measurable D)
    (_h₂ : MemLp D 2 P) (x : B), 0  <  P {s | X s=x} →
    ∀ d d' : ℝ, d ≠ d' → 0  <  profileProbability P X D x d →
      0  <  profileProbability P X D x d' → 0  <  profileVariance P X D x


def SmallWeightFamily : Prop :=
  (∀ (ε : ℝ) (hε : 0  <  ε) (hu : ε  <  1/2),
    IsFiniteLaw (smallWeightPopulation ε) ∧
    (∀ a d, smallWeightOutcome a d = smallWeightOutcome a 0+(1+binaryProfile a)*d) ∧
    finiteUnconfounded (smallWeightPopulation ε) binaryProfile (fun a => (smallWeightOutcome a 0,1+binaryProfile a)) binaryTreatment ∧
    (∀ x ∈ ({0,1} : Finset ℝ),
      finiteCellMean (smallWeightPopulation ε) binaryProfile binaryTreatment x = ε+(1/2-ε)*x ∧
      0  <  finiteCellProbability (smallWeightPopulation ε) binaryProfile binaryTreatment x 0 ∧
      0  <  finiteCellProbability (smallWeightPopulation ε) binaryProfile binaryTreatment x 1) ∧
    finiteMass (finiteEffective (smallWeightPopulation ε) binaryProfile binaryTreatment) (fun a => binaryProfile a=0) =
      ε*(1-ε)/(ε*(1-ε)+1/4) ∧
    0  <  finiteMass (finiteEffective (smallWeightPopulation ε) binaryProfile binaryTreatment) (fun a => binaryProfile a=0) ∧
    finiteMass (finiteEffective (smallWeightPopulation ε) binaryProfile binaryTreatment) (fun a => binaryProfile a=0)  <  4*ε)

def SmallWeightConsistency : Prop :=
  finiteMean (smallWeightPopulation (1/1000000)) (fun a => 1+binaryProfile a) = 3/2 ∧
  (∀ (δ : ℝ) (hδ : 0  <  δ),
    Tendsto (fun n : ℕ => finiteMass (productMass (smallWeightPopulation (1/1000000)) n)
      (fun a => δ  ≤  |sampleMean (smallWeightIPW (1/1000000)) n a-3/2|)) atTop (𝓝 0))

/-- A literal probability measure for the failure of pair-specific positivity. -/
def missingPairPopulation : Measure (Fin 4) := (1/4:ℝ≥0∞) •
  (Measure.dirac 0+Measure.dirac 1+Measure.dirac 2+Measure.dirac 3)

def missingPairProfile : Fin 4 → Fin 2 := ![0,0,1,1]
def missingPairTreatment : Fin 4 → ℝ := ![0,1,0,2]

def MissingPairFailure : Prop :=
  Measurable missingPairProfile ∧ Measurable missingPairTreatment ∧
  MemLp missingPairTreatment 2 missingPairPopulation ∧
  (0:ℝ)≠1 ∧ 0 < missingPairPopulation {i|missingPairTreatment i=0} ∧
  0 < missingPairPopulation {i|missingPairTreatment i=1} ∧
  Integrable (profileWeight missingPairPopulation missingPairProfile missingPairTreatment)
    missingPairPopulation ∧
  (0 < ∫i,profileWeight missingPairPopulation missingPairProfile missingPairTreatment i
    ∂missingPairPopulation) ∧
  0 < effectiveProfileLaw missingPairPopulation missingPairProfile missingPairTreatment
    {i|missingPairProfile i=1} ∧
  profileProbability (effectiveProfileLaw missingPairPopulation missingPairProfile
    missingPairTreatment) missingPairProfile missingPairTreatment 1 1=0

def T17Statement : Prop := DiscretePositivityImplications.{u,v} ∧ SmallWeightFamily ∧
  SmallWeightConsistency ∧ FittedZeroFailure ∧ MissingPairFailure

end
end SAP.P015b
