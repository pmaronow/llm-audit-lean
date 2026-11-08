import SAP.P014.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014
open scoped BigOperators
noncomputable section

def T10GeneralPart : Prop :=
  ∀ {N : ℕ} (L : FiniteDistribution (TreatmentVector N)), IsDistribution L →
  ∀ (S : Finset (Fin N)) (y : PotentialOutcomes N), S.Nonempty →
  (∀ i ∈ S, 0 < armProbability L i true ∧ armProbability L i true < 1) →
  (∀ i ∈ S, ∀ a,
    otherSubjectsAverage L y i a =
      (∑ z ∈ armAssignments L i a, y i z * (L.weight z / armProbability L i a)) ∧
    (∑ z ∈ armAssignments L i a, y i z * (L.weight z / armProbability L i a)) =
      conditionalAverage L y i a) ∧
  windowContrast S (conditionalAverage L y) = -(∑ i ∈ S, directEffect L y i) / S.card ∧
  (∀ m : ℕ, 0 < m → m < S.card →
    (∀ z ∈ L.atoms, armSize S z true = m) →
    (∀ i ∈ S, armProbability L i true = (m : ℝ) / S.card) →
    expectation L (differenceOfMeans S y) = -(∑ i ∈ S, directEffect L y i) / S.card)

def T10FailurePart : Prop :=
  IsDistribution assignmentDistribution ∧ PositiveArms assignmentDistribution localThree ∧
  supportAverage assignmentDistribution outcomes9 0 false ≠
    otherSubjectsAverage assignmentDistribution outcomes9 0 false ∧
  windowContrast localThree (supportAverage assignmentDistribution outcomes9) ≠
    (∑ i ∈ localThree, directEffect assignmentDistribution outcomes9 i) / localThree.card ∧
  windowContrast localThree (supportAverage assignmentDistribution outcomes9) ≠
    -(∑ i ∈ localThree, directEffect assignmentDistribution outcomes9 i) / localThree.card

def T10Statement : Prop := T10GeneralPart ∧ T10FailurePart

end
end SAP.P014
