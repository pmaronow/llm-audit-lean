import SAP.P009a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P009a

open Filter MeasureTheory
open scoped BigOperators Topology Classical

noncomputable section

def ProductDesign {n : ℕ} (E : FiniteExperiment n) : Prop :=
  (∀ i, 0 < armProbability E i true ∧ armProbability E i true < 1) ∧
  ∀ z, E.design.mass z = ∏ i, (if z i then armProbability E i true else 1 - armProbability E i true)

def FixedSizeDesign {n : ℕ} (E : FiniteExperiment n) (m : ℕ) : Prop :=
  0 < m ∧ m < n ∧ ∀ z, E.design.mass z =
    if (∑ i, if z i then (1 : ℕ) else 0) = m then 1 / (n.choose m : ℝ) else 0

def Regularity {n : ℕ} (E : FiniteExperiment n) (k q s : ℝ) : Prop :=
  0 < k ∧ 2 ≤ q ∧ 1 ≤ s ∧
  (∀ i, k⁻¹ ≤ armProbability E i true ∧ armProbability E i true ≤ 1 - k⁻¹) ∧
  (∀ i, expectation E.design (fun z => Real.rpow |E.outcome i z| q) ≤ Real.rpow k q) ∧
  (∀ i b, expectation E.design (fun z => Real.rpow |potentialResponse E i b z| s) ≤ Real.rpow k s)

def relevantTreatments {n : ℕ} (E : FiniteExperiment n) (i : Fin n) (z : TreatmentVector n) : TreatmentVector n :=
  fun j => if Affects E j i then z j else false

def relevantOtherTreatments {n : ℕ} (E : FiniteExperiment n) (i : Fin n) (z : TreatmentVector n) : TreatmentVector n :=
  Function.update (relevantTreatments E i z) i false

def mixingCoefficient {Ω A B : Type*} [Fintype Ω] (P : FiniteDistribution Ω) (X : Ω → A) (Y : Ω → B) : ℝ :=
  sSup {r | ∃ (S : Set A) (T : Set B),
    r = |probability P (fun ω => X ω ∈ S ∧ Y ω ∈ T) -
      probability P (fun ω => X ω ∈ S) * probability P (fun ω => Y ω ∈ T)|}

def mixingPower (a θ : ℝ) : ℝ := if a = 0 then 0 else Real.rpow a θ

def externalMixing {n : ℕ} (E : FiniteExperiment n) (θ : ℝ) : ℝ :=
  (∑ i, ∑ j, (1 - dependenceIndicator E i j) * mixingPower
    (mixingCoefficient E.design (relevantTreatments E i) (relevantTreatments E j)) θ) / n

def internalMixing {n : ℕ} (E : FiniteExperiment n) (θ : ℝ) : ℝ :=
  ∑ i, mixingPower (mixingCoefficient E.design (fun z => z i) (relevantOtherTreatments E i)) θ

def bernoulliVarianceEstimate {n : ℕ} (E : FiniteExperiment n) (z : TreatmentVector n) : ℝ :=
  (∑ i, ((if z i then E.outcome i z ^ 2 else 0) / armProbability E i true ^ 2 +
    (if z i then 0 else E.outcome i z ^ 2) / armProbability E i false ^ 2)) / (n : ℝ) ^ 2

def meanSquaredEffect {n : ℕ} (E : FiniteExperiment n) : ℝ :=
  (∑ i, expectation E.design (individualEffect E i) ^ 2) / n

def expectedSpillover {n : ℕ} (E : FiniteExperiment n) (i j : Fin n) (a : Bool) : ℝ :=
  expectation E.design (fun z =>
    E.outcome i (Function.update (Function.update z i a) j true) -
    E.outcome i (Function.update (Function.update z i a) j false))

def weightedSpillover {n : ℕ} (E : FiniteExperiment n) (i j : Fin n) : ℝ :=
  (1 - armProbability E i true) * expectedSpillover E i j true + armProbability E i true * expectedSpillover E i j false

def weightedOutcome {n : ℕ} (E : FiniteExperiment n) (i : Fin n) : ℝ :=
  (1 - armProbability E i true) * conditionalMean E.design (fun z => z i = true) (E.outcome i) +
  armProbability E i true * conditionalMean E.design (fun z => z i = false) (E.outcome i)

def directBias {n : ℕ} (E : FiniteExperiment n) : ℝ :=
  (∑ i, ∑ j, if j = i then 0 else
    weightedSpillover E i j * weightedSpillover E j i +
    2 * weightedOutcome E j * (expectedSpillover E i j true - expectedSpillover E i j false)) / ((n : ℝ) * averageDependence E)

def indirectBias {n : ℕ} (E : FiniteExperiment n) : ℝ :=
  (∑ i, ∑ j, if j = i then 0 else
    ∑ a : Bool, ∑ b : Bool,
      (1 - 2 * treatmentValue a) * (1 - 2 * treatmentValue b) *
        conditionalCovariance E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j)) /
      ((n : ℝ) * averageDependence E)

def contributionVariance {n : ℕ} (E : FiniteExperiment n) (i : Fin n) : ℝ :=
  variance E.design (fun z => (if z i then E.outcome i z else 0) / armProbability E i true -
    (if z i then 0 else E.outcome i z) / armProbability E i false)

def dispersionOfVariances {n : ℕ} (E : FiniteExperiment n) : ℝ :=
  Real.sqrt ((∑ i, (contributionVariance E i - (∑ j, contributionVariance E j) / n) ^ 2) / n)

def dependenceQuadratic {n : ℕ} (E : FiniteExperiment n) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * dependenceIndicator E i j * v j

def spectralRadius {n : ℕ} (E : FiniteExperiment n) : ℝ :=
  sSup {r | ∃ v : Fin n → ℝ, (∑ i, v i ^ 2) = 1 ∧ r = dependenceQuadratic E v}

def averageVarianceEstimate {n : ℕ} (E : FiniteExperiment n) (z : TreatmentVector n) : ℝ := averageDependence E * bernoulliVarianceEstimate E z

def maximumVarianceEstimate {n : ℕ} (E : FiniteExperiment n) (z : TreatmentVector n) : ℝ := maximumDependence E * bernoulliVarianceEstimate E z

def spectralVarianceEstimate {n : ℕ} (E : FiniteExperiment n) (z : TreatmentVector n) : ℝ := spectralRadius E * bernoulliVarianceEstimate E z

def armResponse {n : ℕ} (E : FiniteExperiment n) (b : Bool) (a : ℕ) (i : Fin n)
    (z : TreatmentVector n) : ℝ := if z i = b then E.outcome i z ^ a else 0

end
end SAP.P009a
