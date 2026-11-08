import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014
open scoped BigOperators
noncomputable section

/-- Distinct atoms and their weights. Validity is a separate premise. Weights
outside `atoms` are immaterial. -/
structure FiniteDistribution (α : Type*) where
  atoms : Finset α
  weight : α → ℝ

def IsDistribution {α : Type*} (L : FiniteDistribution α) : Prop :=
  (∀ x ∈ L.atoms, 0 < L.weight x) ∧ (∑ x ∈ L.atoms, L.weight x) = 1

def expectation {α : Type*} (L : FiniteDistribution α) (f : α → ℝ) : ℝ :=
  ∑ x ∈ L.atoms, L.weight x * f x

def probability {α : Type*} (L : FiniteDistribution α) (P : α → Prop) : ℝ := by
  classical
  exact ∑ x ∈ L.atoms, if P x then L.weight x else 0

def pushforward {α β : Type*} (L : FiniteDistribution α) (f : α → β) :
    FiniteDistribution β := by
  classical
  exact ⟨L.atoms.image f, fun b => probability L (fun a => f a = b)⟩

abbrev TreatmentVector (N : ℕ) := Fin N → Bool
abbrev PotentialOutcomes (N : ℕ) := Fin N → TreatmentVector N → ℝ

def binaryValue (a : Bool) : ℝ := if a then 1 else 0

def thresholdAssignment {N : ℕ} (x : Fin N → ℝ) : TreatmentVector N :=
  fun i => decide (0 ≤ x i)

def insideWindow (b x : ℝ) : Prop := -b ≤ x ∧ x ≤ b

def windowSubjects {N : ℕ} (b : ℝ) (x : Fin N → ℝ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i => insideWindow b (x i))

def windowCDF {N : ℕ} (S : Finset (Fin N)) (x : Fin N → ℝ) (t : ℝ) : ℝ := by
  classical
  exact (∑ i ∈ S, if x i ≤ t then (1 : ℝ) else 0) / S.card

def armAssignments {N : ℕ} (L : FiniteDistribution (TreatmentVector N))
    (i : Fin N) (a : Bool) : Finset (TreatmentVector N) :=
  L.atoms.filter (fun z => z i = a)

def armProbability {N : ℕ} (L : FiniteDistribution (TreatmentVector N))
    (i : Fin N) (a : Bool) : ℝ := ∑ z ∈ armAssignments L i a, L.weight z

def armMoment {N : ℕ} (L : FiniteDistribution (TreatmentVector N))
    (y : PotentialOutcomes N) (i : Fin N) (a : Bool) : ℝ :=
  ∑ z ∈ armAssignments L i a, L.weight z * y i z

/-- The printed average counts each supported assignment once. -/
def supportAverage {N : ℕ} (L : FiniteDistribution (TreatmentVector N))
    (y : PotentialOutcomes N) (i : Fin N) (a : Bool) : ℝ :=
  (∑ z ∈ armAssignments L i a, y i z) / (armAssignments L i a).card

/-- Conditional expectation given the positive-probability event `Z i = a`. -/
def conditionalAverage {N : ℕ} (L : FiniteDistribution (TreatmentVector N))
    (y : PotentialOutcomes N) (i : Fin N) (a : Bool) : ℝ :=
  armMoment L y i a / armProbability L i a

def windowContrast {N : ℕ} (S : Finset (Fin N)) (f : Fin N → Bool → ℝ) : ℝ :=
  (∑ i ∈ S, (f i true - f i false)) / S.card

def armSize {N : ℕ} (S : Finset (Fin N)) (z : TreatmentVector N) (a : Bool) : ℝ :=
  ∑ i ∈ S, if z i = a then (1 : ℝ) else 0

def observedArmTotal {N : ℕ} (S : Finset (Fin N)) (y : PotentialOutcomes N)
    (z : TreatmentVector N) (a : Bool) : ℝ :=
  ∑ i ∈ S, if z i = a then y i z else 0

def differenceOfMeans {N : ℕ} (S : Finset (Fin N)) (y : PotentialOutcomes N)
    (z : TreatmentVector N) : ℝ :=
  observedArmTotal S y z true / armSize S z true -
    observedArmTotal S y z false / armSize S z false

def ConditionallyUniform {N : ℕ} (L : FiniteDistribution (TreatmentVector N))
    (S : Finset (Fin N)) : Prop :=
  ∀ i ∈ S, ∀ a, ∀ z ∈ armAssignments L i a,
    L.weight z / armProbability L i a = 1 / ((armAssignments L i a).card : ℝ)

def Noninterfering {N : ℕ} (S : Finset (Fin N)) (y : PotentialOutcomes N) : Prop :=
  ∀ i ∈ S, ∀ z z', z i = z' i → y i z = y i z'

def PositiveArms {N : ℕ} (L : FiniteDistribution (TreatmentVector N))
    (S : Finset (Fin N)) : Prop :=
  ∀ i ∈ S, ∀ a, 0 < armProbability L i a

def DistinctNoTies {Ω : Type*} {N : ℕ} (L : FiniteDistribution Ω)
    (X : Ω → Fin N → ℝ) (S : Finset (Fin N)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → probability L (fun ω => X ω i = X ω j) = 0

/-- Printed formal clauses, with no ties read for distinct subjects, as
specified by standing assumption R6. -/
def PrintedLocalConditions {Ω : Type*} {N : ℕ} (L : FiniteDistribution Ω)
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) : Prop :=
  (∀ ω ∈ L.atoms, windowSubjects b (X ω) = S) ∧
  (∃ F : ℝ → ℝ, ∀ ω ∈ L.atoms, ∀ t, windowCDF S (X ω) t = F t) ∧
  (∀ ω ∈ L.atoms, probability L (fun η => X η = X ω) =
    1 / (S.card.factorial : ℝ)) ∧
  DistinctNoTies L X S ∧
  (∀ ω ∈ L.atoms, 0 < armSize S (thresholdAssignment (X ω)) true ∧
    armSize S (thresholdAssignment (X ω)) true < S.card)

abbrev OtherTreatments {N : ℕ} (i : Fin N) := {j : Fin N // j ≠ i} → Bool

def removeOwn {N : ℕ} (i : Fin N) (z : TreatmentVector N) : OtherTreatments i :=
  fun j => z j

def insertOwn {N : ℕ} (i : Fin N) (a : Bool) (u : OtherTreatments i) :
    TreatmentVector N := (Equiv.funSplitAt i Bool).symm (a, u)

def conditionalOtherProbability {N : ℕ} (L : FiniteDistribution (TreatmentVector N))
    (i : Fin N) (a : Bool) (u : OtherTreatments i) : ℝ :=
  probability L (fun z => z i = a ∧ removeOwn i z = u) / armProbability L i a

def otherSubjectsAverage {N : ℕ} (L : FiniteDistribution (TreatmentVector N))
    (y : PotentialOutcomes N) (i : Fin N) (a : Bool) : ℝ :=
  ∑ u : OtherTreatments i, y i (insertOwn i a u) * conditionalOtherProbability L i a u

/-- Hudgens--Halloran's control-minus-treatment sign convention. -/
def directEffect {N : ℕ} (L : FiniteDistribution (TreatmentVector N))
    (y : PotentialOutcomes N) (i : Fin N) : ℝ :=
  otherSubjectsAverage L y i false - otherSubjectsAverage L y i true

end
end SAP.P014
