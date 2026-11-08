import SAP.P026a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section


/-- Mathematical content of target P026-T1. -/
def T1Statement : Prop :=
  (isProbability asymmetricPairLaw ∧ hasPositiveMarginals asymmetricPairLaw ∧
    (∀ i j : Fin 2, i ≠ j → 0 < disagreementProbability asymmetricPairLaw i j ∧
      0 < jointInclusion asymmetricPairLaw true true i j ∧ 0 < jointInclusion asymmetricPairLaw false false i j) ∧
    jointInclusion asymmetricPairLaw true false 0 1 = 0 ∧
    jointInclusion asymmetricPairLaw true false 1 0 = 1/3 ∧
    (∀ w : Fin 3, armIndicator asymmetricPairLaw true w 0 * armIndicator asymmetricPairLaw false w 1 = 0) ∧
    (∀ w : Fin 3, htContrast asymmetricPairLaw 2 (fun _ => 1) (fun _ => 1) w = (![-9/4, 0, 9/4] : Fin 3 → ℚ) w) ∧
    (∀ w : Fin 3, printedVarianceEstimate asymmetricPairLaw 2 (fun _ => 1) (fun _ => 1) w = (![57/16, 3/2, 57/16] : Fin 3 → ℚ) w) ∧
    mean asymmetricPairLaw (htContrast asymmetricPairLaw 2 (fun _ => 1) (fun _ => 1)) = 0 ∧
    designVariance asymmetricPairLaw (htContrast asymmetricPairLaw 2 (fun _ => 1) (fun _ => 1)) = 27/8 ∧
    mean asymmetricPairLaw (printedVarianceEstimate asymmetricPairLaw 2 (fun _ => 1) (fun _ => 1)) = 23/8 ∧
    (23/8 : ℚ) < 27/8 ∧
    designCovariance asymmetricPairLaw (htSum asymmetricPairLaw true (fun _ => 1))
      (htSum asymmetricPairLaw false (fun _ => 1)) = -13/4 ∧
    mean asymmetricPairLaw (covarianceWithZeroOmission asymmetricPairLaw (fun _ => 1) (fun _ => 1)) = -9/4 ∧
    (-13/4 : ℚ) < -9/4) ∧
  (isProbability asymmetricSixLaw ∧ hasPositiveMarginals asymmetricSixLaw ∧
    (∀ w : Fin 14, (∑ i : Fin 6, armIndicator asymmetricSixLaw true w i) = 3) ∧
    (∀ i j : Fin 6, i ≠ j → 0 < disagreementProbability asymmetricSixLaw i j ∧
      0 < jointInclusion asymmetricSixLaw true true i j ∧ 0 < jointInclusion asymmetricSixLaw false false i j) ∧
    (∀ i j : Fin 6, i ≠ j → (jointInclusion asymmetricSixLaw true false i j = 0 ↔ i = 0 ∧ j = 1)) ∧
    designVariance asymmetricSixLaw (htContrast asymmetricSixLaw 6 (fun _ => 1) (fun _ => 1)) = 9/700 ∧
    mean asymmetricSixLaw (printedVarianceEstimate asymmetricSixLaw 6 (fun _ => 1) (fun _ => 1)) = -269/6300 ∧
    (-269/6300 : ℚ) < 9/700 ∧
    designCovariance asymmetricSixLaw (htSum asymmetricSixLaw true (fun _ => 1))
      (htSum asymmetricSixLaw false (fun _ => 1)) = 27/175 ∧
    mean asymmetricSixLaw (covarianceWithZeroOmission asymmetricSixLaw (fun _ => 1) (fun _ => 1)) = 202/175)

end
end SAP.P026a
