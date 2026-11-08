import SAP.P026a.Defs.Part15

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section


/-- Mathematical content of target P026-T12. -/
def T12Statement : Prop :=
  (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitLaw I) (x z : I → ℝ),
    designVariance E.assignmentDesign (htContrast E.assignmentDesign (Fintype.card I) x z) =
      (designVariance E.assignmentDesign (htSum E.assignmentDesign true x) +
        designVariance E.assignmentDesign (htSum E.assignmentDesign false z) -
        2 * designCovariance E.assignmentDesign (htSum E.assignmentDesign true x)
          (htSum E.assignmentDesign false z)) / (Fintype.card I : ℝ)^2) ∧
  (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitLaw I) (a : Bool) (y : I → ℝ),
    designVariance E.assignmentDesign (htSum E.assignmentDesign a y) =
      (∑ i, ∑ j, designCovariance E.assignmentDesign
        (fun w => armIndicator E.assignmentDesign a w i)
        (fun w => armIndicator E.assignmentDesign a w j) *
        (y i / inclusion E.assignmentDesign a i) * (y j / inclusion E.assignmentDesign a j)) ∧
    designVariance E.assignmentDesign (htSum E.assignmentDesign a y) =
      (∑ i, designVariance E.assignmentDesign (fun w => armIndicator E.assignmentDesign a w i) *
        (y i / inclusion E.assignmentDesign a i)^2) +
      orderedOffDiagonalSum (fun i j => designCovariance E.assignmentDesign
        (fun w => armIndicator E.assignmentDesign a w i)
        (fun w => armIndicator E.assignmentDesign a w j) *
        (y i / inclusion E.assignmentDesign a i) * (y j / inclusion E.assignmentDesign a j)) ∧
    designVariance E.assignmentDesign (htSum E.assignmentDesign a y) =
      armPopulationVariance E.assignmentDesign a y) ∧
  (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitLaw I)
    (a b :  Bool)
    (x z :  I → ℝ),
    designCovariance E.assignmentDesign (htSum E.assignmentDesign a x) (htSum E.assignmentDesign b z) =
      ∑ i, ∑ j, (jointInclusion E.assignmentDesign a b i j - inclusion E.assignmentDesign a i * inclusion E.assignmentDesign b j) *
        (x i / inclusion E.assignmentDesign a i) * (z j / inclusion E.assignmentDesign b j)) ∧
  (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitLaw I)
    (x z :  I → ℝ),
    designVariance E.assignmentDesign (htContrast E.assignmentDesign (Fintype.card I) x z) =
      (armPopulationVariance E.assignmentDesign true x + armPopulationVariance E.assignmentDesign false z -
        2*splitPopulationCovariance E.assignmentDesign x z) / ((Fintype.card I) : ℝ)^2) ∧
  (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitLaw I)
    (x z :  I → ℝ),
    designCovariance E.assignmentDesign (htSum E.assignmentDesign true x) (htSum E.assignmentDesign false z) = splitPopulationCovariance E.assignmentDesign x z)

end
end SAP.P026a
