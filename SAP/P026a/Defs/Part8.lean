import SAP.P026a.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section


/-- Mathematical content of target P026-T4. -/
def T4Statement : Prop :=
  (isProbability xorSixLaw ∧ hasPositiveMarginals xorSixLaw ∧
    (∀ i : Fin 6, inclusion xorSixLaw true i = 1/2 ∧ inclusion xorSixLaw false i = 1/2) ∧
    (∀ i j : Fin 6, i.val / 2 ≠ j.val / 2 →
      ∀ a b : Bool, jointInclusion xorSixLaw a b i j = 1/4) ∧
    (∀ w : Fin 4, (∑ i : Fin 6, armIndicator xorSixLaw true w i) = 3) ∧
    (∀ w i, xorSixFit w i = armIndicator xorSixLaw true w i) ∧
    (∀ i, designCovariance xorSixLaw (fun w => armIndicator xorSixLaw true w i)
      (fun w => xorSixFit w i) = 1/4) ∧
    (∀ w, adjustedSum xorSixLaw true (fun _ => 1) xorSixFit w = 3 ∧
      adjustedSum xorSixLaw false (fun _ => 0) xorSixFit w = 3 ∧
      adjustedContrast xorSixLaw 6 (fun _ => 1) (fun _ => 0) xorSixFit w = 0 ∧
      htContrast xorSixLaw 6 (fun _ => 1) (fun _ => 0) w = 1) ∧
    averageEffect 6 (fun _ : Fin 6 => (1 : ℚ)) (fun _ => 0) = 1 ∧
    mean xorSixLaw (adjustedContrast xorSixLaw 6 (fun _ => 1) (fun _ => 0) xorSixFit) -
      averageEffect 6 (fun _ : Fin 6 => (1 : ℚ)) (fun _ => 0) = -1) ∧
  (isProbability xorThreeLaw ∧ hasPositiveMarginals xorThreeLaw ∧
    (∀ i j : Fin 3, i ≠ j → ∀ a b : Bool, jointInclusion xorThreeLaw a b i j = 1/4) ∧
    (∀ w i, xorThreeFit w i = armIndicator xorThreeLaw true w i) ∧
    (∀ i, designCovariance xorThreeLaw (fun w => armIndicator xorThreeLaw true w i)
      (fun w => xorThreeFit w i) = 1/4) ∧
    mean xorThreeLaw (adjustedContrast xorThreeLaw 3 (fun _ => 1) (fun _ => 0) xorThreeFit) = 0 ∧
    designCovariance xorThreeLaw (fun w => armIndicator xorThreeLaw true w 2)
      (fun w => productFit w 2) = -1/8 ∧
    mean xorThreeLaw (adjustedContrast xorThreeLaw 3 (fun _ => 1) (fun _ => 0) productFit) = 7/6 ∧
    averageEffect 3 (fun _ : Fin 3 => (1 : ℚ)) (fun _ => 0) = 1)

end
end SAP.P026a
