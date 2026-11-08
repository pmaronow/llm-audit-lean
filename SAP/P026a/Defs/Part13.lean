import SAP.P026a.Defs.Part12

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section


/-- Mathematical content of target P026-T9. -/
def T9Statement : Prop :=
  (isProbability twoOfFourLaw ∧ hasPositiveMarginals twoOfFourLaw ∧ directedSupport twoOfFourLaw ∧
    (∀ i j : Fin 4, i ≠ j → jointInclusion twoOfFourLaw true true i j = 1/6 ∧
      jointInclusion twoOfFourLaw false false i j = 1/6 ∧ jointInclusion twoOfFourLaw true false i j = 1/3) ∧
    (∀ w, appendixDisplay twoOfFourLaw appendixNullOutcomes appendixNullOutcomes w =
      (![-68,-52,2,-62,-20,-52] : Fin 6 → ℚ) w) ∧
    mean twoOfFourLaw (appendixDisplay twoOfFourLaw appendixNullOutcomes appendixNullOutcomes) = -42 ∧
    designCovariance twoOfFourLaw (htSum twoOfFourLaw true appendixNullOutcomes)
      (htSum twoOfFourLaw false appendixNullOutcomes) = -28 ∧
    populationCrossCovariance twoOfFourLaw appendixNullOutcomes appendixNullOutcomes = -28 ∧
    mean twoOfFourLaw (covarianceWithZeroOmission twoOfFourLaw appendixNullOutcomes appendixNullOutcomes) = -28 ∧
    designVariance twoOfFourLaw (htSum twoOfFourLaw true appendixNullOutcomes) = 28 ∧
    (-42 : ℚ) ≠ -28) ∧
  (populationCovarianceBound twoOfFourLaw appendixNullOutcomes appendixNullOutcomes = -28)

end
end SAP.P026a
