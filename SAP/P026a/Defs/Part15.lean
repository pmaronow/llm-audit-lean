import SAP.P026a.Defs.Part14

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section


/-- Mathematical content of target P026-T11. -/
def T11Statement : Prop :=
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (a :  Bool)
    (y : U → ℝ),
    designVariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign a (E.totals y)) = armPopulationVariance E.clusterAssignmentDesign a (E.totals y)) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (a :  Bool)
    (x z : U → ℝ),
    let y := if a then (E.totals x) else (E.totals z)
    armPopulationBound E.clusterAssignmentDesign a y - designVariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign a y) =
      unavailablePairSum E.clusterAssignmentDesign a a (fun i j => (y i+y j)^2) / 2 ∧
    mean E.clusterAssignmentDesign (armVarianceEstimate E.clusterAssignmentDesign a (E.totals x) (E.totals z)) = armPopulationBound E.clusterAssignmentDesign a y ∧
    designVariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign a y) ≤ mean E.clusterAssignmentDesign (armVarianceEstimate E.clusterAssignmentDesign a (E.totals x) (E.totals z)) ∧
    ((∀ i j, i ≠ j → 0 < jointInclusion E.clusterAssignmentDesign a a i j) →
      mean E.clusterAssignmentDesign (armVarianceEstimate E.clusterAssignmentDesign a (E.totals x) (E.totals z)) = designVariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign a y))) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (a : Bool) (x z : U → ℝ)
    (hs : ∀ i j, i ≠ j → 0 < jointInclusion E.clusterAssignmentDesign a a i j),
    mean E.clusterAssignmentDesign (fullSupportArmEstimate E.clusterAssignmentDesign a (E.totals x) (E.totals z)) =
      designVariance E.clusterAssignmentDesign
        (htSum E.clusterAssignmentDesign a (if a then E.totals x else E.totals z)))

end
end SAP.P026a
