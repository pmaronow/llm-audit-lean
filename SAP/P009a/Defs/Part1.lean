import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P009a

open Filter MeasureTheory
open scoped BigOperators Topology Classical

noncomputable section

abbrev TreatmentVector (n : ℕ) := Fin n → Bool

def treatmentValue (b : Bool) : ℝ := if b then 1 else 0

structure FiniteDistribution (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

def expectation {Ω : Type*} [Fintype Ω] (P : FiniteDistribution Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, P.mass ω * X ω

def probability {Ω : Type*} [Fintype Ω] (P : FiniteDistribution Ω) (A : Ω → Prop) : ℝ :=
  expectation P (fun ω => if A ω then 1 else 0)

def conditionalMean {Ω : Type*} [Fintype Ω] (P : FiniteDistribution Ω) (A : Ω → Prop) (X : Ω → ℝ) : ℝ :=
  expectation P (fun ω => if A ω then X ω else 0) / probability P A

def covariance {Ω : Type*} [Fintype Ω] (P : FiniteDistribution Ω) (X Y : Ω → ℝ) : ℝ :=
  expectation P (fun ω => (X ω - expectation P X) * (Y ω - expectation P Y))

def variance {Ω : Type*} [Fintype Ω] (P : FiniteDistribution Ω) (X : Ω → ℝ) : ℝ := covariance P X X

def conditionalCovariance {Ω : Type*} [Fintype Ω] (P : FiniteDistribution Ω) (A : Ω → Prop) (X Y : Ω → ℝ) : ℝ :=
  conditionalMean P A (fun ω => (X ω - conditionalMean P A X) * (Y ω - conditionalMean P A Y))

structure FiniteExperiment (n : ℕ) where
  design : FiniteDistribution (TreatmentVector n)
  outcome : Fin n → TreatmentVector n → ℝ

def armProbability {n : ℕ} (E : FiniteExperiment n) (i : Fin n) (b : Bool) : ℝ :=
  probability E.design (fun z => z i = b)

def potentialResponse {n : ℕ} (E : FiniteExperiment n) (i : Fin n) (b : Bool)
    (z : TreatmentVector n) : ℝ := E.outcome i (Function.update z i b)

def individualEffect {n : ℕ} (E : FiniteExperiment n) (i : Fin n) (z : TreatmentVector n) : ℝ :=
  potentialResponse E i true z - potentialResponse E i false z

def assignmentATE {n : ℕ} (E : FiniteExperiment n) (z : TreatmentVector n) : ℝ :=
  (∑ i, individualEffect E i z) / n

def NoSpillovers {n : ℕ} (E : FiniteExperiment n) : Prop :=
  ∀ i z z', z i = z' i → E.outcome i z = E.outcome i z'

def expectedATE {n : ℕ} (E : FiniteExperiment n) : ℝ := expectation E.design (assignmentATE E)

def distributionalEffect {n : ℕ} (E : FiniteExperiment n) : ℝ :=
  (∑ i, (conditionalMean E.design (fun z => z i = true) (E.outcome i) -
    conditionalMean E.design (fun z => z i = false) (E.outcome i))) / n

def estimatedArmMean {n : ℕ} (E : FiniteExperiment n) (b : Bool) (z : TreatmentVector n) : ℝ :=
  (∑ i, (if z i = b then E.outcome i z else 0) / armProbability E i b) / n

def estimatedArmSize {n : ℕ} (E : FiniteExperiment n) (b : Bool) (z : TreatmentVector n) : ℝ :=
  ∑ i, (if z i = b then (1 : ℝ) else 0) / armProbability E i b

def htEstimate {n : ℕ} (E : FiniteExperiment n) (z : TreatmentVector n) : ℝ :=
  estimatedArmMean E true z - estimatedArmMean E false z

def Affects {n : ℕ} (E : FiniteExperiment n) (i j : Fin n) : Prop :=
  i = j ∨ ∃ z z', (∀ ℓ, ℓ ≠ i → z ℓ = z' ℓ) ∧ E.outcome j z ≠ E.outcome j z'

def interferenceIndicator {n : ℕ} (E : FiniteExperiment n) (i j : Fin n) : ℝ :=
  if Affects E i j then 1 else 0

def SharesCause {n : ℕ} (E : FiniteExperiment n) (i j : Fin n) : Prop :=
  ∃ ℓ, Affects E ℓ i ∧ Affects E ℓ j

def dependenceIndicator {n : ℕ} (E : FiniteExperiment n) (i j : Fin n) : ℝ :=
  if SharesCause E i j then 1 else 0

def dependenceDegree {n : ℕ} (E : FiniteExperiment n) (i : Fin n) : ℝ := ∑ j, dependenceIndicator E i j

def averageDependence {n : ℕ} (E : FiniteExperiment n) : ℝ := (∑ i, dependenceDegree E i) / n

def outgoingCount {n : ℕ} (E : FiniteExperiment n) (i : Fin n) : ℝ := ∑ j, interferenceIndicator E i j

def incomingCount {n : ℕ} (E : FiniteExperiment n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => Affects E j i)).card

def averageOutgoing {n : ℕ} (E : FiniteExperiment n) : ℝ := (∑ i, outgoingCount E i) / n

def maximumOutgoing {n : ℕ} (E : FiniteExperiment n) : ℝ := sSup (Set.range (outgoingCount E))

def maximumDependence {n : ℕ} (E : FiniteExperiment n) : ℝ := sSup (Set.range (dependenceDegree E))

def rmsDependence {n : ℕ} (E : FiniteExperiment n) : ℝ := Real.sqrt ((∑ i, dependenceDegree E i ^ 2) / n)

end
end SAP.P009a
