import SAP.P014.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014
open scoped BigOperators
noncomputable section
universe u

/-- Assignment-law part of T2, including its four displayed derivation steps. -/
def T2Statement : Prop :=
  ∀ {N : ℕ} (L : FiniteDistribution (TreatmentVector N)), IsDistribution L →
  ∀ (S : Finset (Fin N)) (y : PotentialOutcomes N) (m : ℕ),
  0 < m → m < S.card →
  (∀ z ∈ L.atoms, armSize S z true = m) →
  (∀ i ∈ S, armProbability L i true = (m : ℝ) / S.card) →
  PositiveArms L S ∧
  (∀ i ∈ S, ∀ a, armProbability L i a = probability L (fun z => z i = a)) ∧
  (∀ i ∈ S, armProbability L i false = ((S.card : ℝ) - m) / S.card) ∧
  (∀ z ∈ L.atoms, armSize S z false = (S.card : ℝ) - m ∧
    differenceOfMeans S y z = observedArmTotal S y z true / m -
      observedArmTotal S y z false / ((S.card : ℝ) - m)) ∧
  (∀ i ∈ S, ∀ a,
    expectation L (fun z => if z i = a then y i z else 0) = armMoment L y i a ∧
    armMoment L y i a = armProbability L i a * conditionalAverage L y i a) ∧
  (∀ i ∈ S,
    armMoment L y i true = ((m : ℝ) / S.card) * conditionalAverage L y i true ∧
    armMoment L y i false = (((S.card : ℝ) - m) / S.card) *
      conditionalAverage L y i false) ∧
  expectation L (differenceOfMeans S y) =
    (∑ i ∈ S, armMoment L y i true) / m -
      (∑ i ∈ S, armMoment L y i false) / ((S.card : ℝ) - m) ∧
  expectation L (differenceOfMeans S y) =
    (1 / (m : ℝ)) * ((m : ℝ) / S.card) * (∑ i ∈ S, conditionalAverage L y i true) -
      (1 / ((S.card : ℝ) - m)) * (((S.card : ℝ) - m) / S.card) *
        (∑ i ∈ S, conditionalAverage L y i false) ∧
  expectation L (differenceOfMeans S y) = windowContrast S (conditionalAverage L y) ∧
  windowContrast S (conditionalAverage L y) =
    ((∑ i ∈ S, conditionalAverage L y i true) -
      ∑ i ∈ S, conditionalAverage L y i false) / S.card

def T3ConditionalPart : Prop :=
  ∀ {N : ℕ} (L : FiniteDistribution (TreatmentVector N)), IsDistribution L →
  ∀ (S : Finset (Fin N)) (y : PotentialOutcomes N) (m : ℕ),
  0 < m → m < S.card →
  (∀ z ∈ L.atoms, armSize S z true = m) →
  (∀ i ∈ S, armProbability L i true = (m : ℝ) / S.card) →
  ConditionallyUniform L S →
  (∀ i ∈ S, ∀ a, (armAssignments L i a).Nonempty ∧
    supportAverage L y i a = conditionalAverage L y i a) ∧
  expectation L (differenceOfMeans S y) = windowContrast S (supportAverage L y) ∧
  windowContrast S (supportAverage L y) =
    ((∑ i ∈ S, supportAverage L y i true) - ∑ i ∈ S, supportAverage L y i false) / S.card

def T3UniformPart : Prop :=
  ∀ {N : ℕ} (L : FiniteDistribution (TreatmentVector N)), IsDistribution L →
  ∀ S : Finset (Fin N),
  (∀ z ∈ L.atoms, L.weight z = 1 / (L.atoms.card : ℝ)) → ConditionallyUniform L S

def T3FixedOutsidePart : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {N : ℕ}
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (v : S → ℝ)
    (A : FiniteDistribution (TreatmentVector N)), IsDistribution A →
  ∀ (c : TreatmentVector N) (y : PotentialOutcomes N) (m : ℕ),
  0 < b → Function.Injective v → (∀ i, insideWindow b (v i)) →
  0 < m → m < S.card →
  (Finset.univ.filter (fun i : S => 0 ≤ v i)).card = m →
  CorrectedLocalConditions μ X b S v →
  (∀ z : TreatmentVector N, eventProbability μ (fun ω => thresholdAssignment (X ω) = z) =
    if z ∈ A.atoms then A.weight z else 0) →
  (∀ᵐ ω ∂μ, ∀ i ∉ S, thresholdAssignment (X ω) i = c i) →
  A.atoms.card = S.card.choose m ∧
  (∀ z ∈ A.atoms,
    (Finset.univ.filter (fun σ : Equiv.Perm S => permutationAssignment S v c σ = z)).card =
      m.factorial * (S.card - m).factorial ∧
    A.weight z = (m.factorial : ℝ) * (S.card - m).factorial / S.card.factorial ∧
    A.weight z = 1 / (S.card.choose m : ℝ)) ∧
  (∀ z ∈ A.atoms, armSize S z true = m) ∧
  (∀ i ∈ S, armProbability A i true = (m : ℝ) / S.card) ∧
  ConditionallyUniform A S ∧
  expectation A (differenceOfMeans S y) = windowContrast S (supportAverage A y) ∧
  (∀ z : TreatmentVector N, (∀ i ∉ S, z i = c i) → armSize S z true = m →
    z ∈ A.atoms ∧
    (Finset.univ.filter (fun σ : Equiv.Perm S => permutationAssignment S v c σ = z)).card =
      m.factorial * (S.card - m).factorial ∧
    A.weight z = 1 / (S.card.choose m : ℝ))

def T3NoninterferencePart : Prop :=
  ∀ {N : ℕ} (L : FiniteDistribution (TreatmentVector N)), IsDistribution L →
  ∀ (S : Finset (Fin N)) (y : PotentialOutcomes N) (m : ℕ),
  0 < m → m < S.card →
  (∀ z ∈ L.atoms, armSize S z true = m) →
  (∀ i ∈ S, armProbability L i true = (m : ℝ) / S.card) → Noninterfering S y →
  (∀ i ∈ S, ∀ a, ∀ z : TreatmentVector N, z i = a →
    supportAverage L y i a = y i z ∧ conditionalAverage L y i a = y i z) ∧
  expectation L (differenceOfMeans S y) = windowContrast S (supportAverage L y)

def T3NecessityPart : Prop :=
  ∀ {N : ℕ} (L : FiniteDistribution (TreatmentVector N)), IsDistribution L →
  ∀ (i : Fin N) (a : Bool), 0 < armProbability L i a →
  (∀ y : PotentialOutcomes N, supportAverage L y i a = conditionalAverage L y i a) →
  ∀ z ∈ armAssignments L i a,
    L.weight z / armProbability L i a = 1 / ((armAssignments L i a).card : ℝ)

def T3Statement : Prop :=
  T3ConditionalPart ∧ T3UniformPart ∧ T3FixedOutsidePart.{u} ∧
    T3NoninterferencePart ∧ T3NecessityPart

end
end SAP.P014
