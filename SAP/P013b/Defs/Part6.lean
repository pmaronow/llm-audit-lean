import Mathlib
import SAP.P013b.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P013b
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]


def T21Statement : Prop :=
  ((∀ i, pi locationPopulation i 1 = locationDesign.weight i) ∧
    (∀ i, pi locationPopulation i 0 = 1 - locationDesign.weight i) ∧
    (∀ d, Positivity locationPopulation d) ∧
    (∀ i d, locationPopulation.outcome i d = locationPrediction i) ∧
    (∀ i, covariance locationDesign (fun _ => locationPrediction i)
      (fun z => indicator locationPopulation.exposure i 1 z) = 0) ∧
    (∀ z, (∑ i, indicator locationPopulation.exposure i 1 z) = 1 ∧
      (∑ i, indicator locationPopulation.exposure i 0 z) = 2)) ∧
  ((∀ d, potentialTotal locationPopulation d = 10 ∧
      potentialTotal (shiftPopulation locationPopulation 1) d = 13) ∧
    causalEffect locationPopulation 1 0 = 0 ∧
    causalEffect (shiftPopulation locationPopulation 1) 1 0 = 0 ∧
    (∀ z d, differenceTotal locationPopulation d locationPrediction z = 10) ∧
    (∀ z, differenceEffect locationPopulation 1 0 locationPrediction locationPrediction z = 0)) ∧
  (∀ z : Fin 3,
      htCount locationPopulation 1 z = (if z = 2 then 2 else 4) ∧
      htCount locationPopulation 0 z = (if z = 2 then 8/3 else 10/3) ∧
      differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction z =
        (if z = 2 then 12 else 14) ∧
      differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction z =
        (if z = 2 then 38/3 else 40/3) ∧
      differenceEffect (shiftPopulation locationPopulation 1) 1 0
        locationPrediction locationPrediction z = (if z = 2 then -2/9 else 2/9)) ∧
  ((∀ d, Positivity locationPopulation d) ∧
    (∀ i, covariance locationDesign (fun _ => locationPrediction i)
      (fun z => indicator locationPopulation.exposure i 1 z) = 0) ∧
    (∀ z, (∑ i, indicator locationPopulation.exposure i 1 z) = 1 ∧
      (∑ i, indicator locationPopulation.exposure i 0 z) = 2) ∧
    causalEffect (shiftPopulation locationPopulation 1) 1 0 = causalEffect locationPopulation 1 0 ∧
    (∀ z, differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction z ≠
      differenceTotal locationPopulation 1 locationPrediction z + 1 * (3 : ℝ) ∧
      differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction z ≠
        differenceTotal locationPopulation 0 locationPrediction z + 1 * (3 : ℝ) ∧
      differenceEffect (shiftPopulation locationPopulation 1) 1 0 locationPrediction locationPrediction z ≠
        differenceEffect locationPopulation 1 0 locationPrediction locationPrediction z)) ∧
  (expectation locationDesign (differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction) = 13 ∧
    expectation locationDesign (differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction) = 13 ∧
    expectation locationDesign (differenceEffect (shiftPopulation locationPopulation 1) 1 0
      locationPrediction locationPrediction) = 0 ∧
    variance locationDesign (differenceTotal locationPopulation 1 locationPrediction) = 0 ∧
    variance locationDesign (differenceTotal locationPopulation 0 locationPrediction) = 0 ∧
    variance locationDesign (differenceEffect locationPopulation 1 0 locationPrediction locationPrediction) = 0 ∧
    variance locationDesign (differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction) = 1 ∧
    variance locationDesign (differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction) = 1/9 ∧
    variance locationDesign (differenceEffect (shiftPopulation locationPopulation 1) 1 0
      locationPrediction locationPrediction) = 4/81) ∧
  (∀ z, (∀ d, differenceTotal (shiftPopulation locationPopulation 1) d
      (fun i => locationPrediction i + 1) z = 13) ∧
    differenceEffect (shiftPopulation locationPopulation 1) 1 0
      (fun i => locationPrediction i + 1) (fun i => locationPrediction i + 1) z = 0) ∧
  (∀ z i,
    observed locationPopulation z i - locationPrediction i = 0 ∧
    observed (shiftPopulation locationPopulation 1) z i - locationPrediction i = 1 ∧
    observed (shiftPopulation locationPopulation 1) z i - (locationPrediction i + 1) = 0) ∧
  (∀ z : Fin 3,
    differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction z =
      10 + htCount locationPopulation 1 z ∧
    differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction z =
      10 + htCount locationPopulation 0 z ∧
    differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction z -
      differenceTotal locationPopulation 1 locationPrediction z - 3 =
      (if z = 2 then -1 else 1) ∧
    differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction z -
      differenceTotal locationPopulation 0 locationPrediction z - 3 =
      (if z = 2 then -(1/3) else 1/3) ∧
    differenceEffect (shiftPopulation locationPopulation 1) 1 0 locationPrediction locationPrediction z -
      differenceEffect locationPopulation 1 0 locationPrediction locationPrediction z =
      (htCount locationPopulation 1 z - htCount locationPopulation 0 z) / 3 ∧
    differenceEffect (shiftPopulation locationPopulation 1) 1 0 locationPrediction locationPrediction z -
      differenceEffect locationPopulation 1 0 locationPrediction locationPrediction z =
      (if z = 2 then -2/9 else 2/9))

end
end SAP.P013b
