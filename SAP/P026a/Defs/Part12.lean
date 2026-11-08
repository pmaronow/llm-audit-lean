import SAP.P026a.Defs.Part11

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section


/-- Mathematical content of target P026-T8. -/
def T8Statement : Prop :=
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (x z : U → ℝ),
    designCovariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign true (E.totals x)) (htSum E.clusterAssignmentDesign false (E.totals z)) =
      populationCrossCovariance E.clusterAssignmentDesign (E.totals x) (E.totals z)) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (x z : U → ℝ),
    designCovariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign true (E.totals x)) (htSum E.clusterAssignmentDesign false (E.totals z)) - populationCovarianceBound E.clusterAssignmentDesign (E.totals x) (E.totals z) =
      (∑ i, ((E.totals x) i-(E.totals z) i)^2) / 2) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (hc :  directedSupport E.clusterAssignmentDesign)
    (x z : U → ℝ),
    mean E.clusterAssignmentDesign (covarianceWithZeroOmission E.clusterAssignmentDesign (E.totals x) (E.totals z)) = populationCovarianceBound E.clusterAssignmentDesign (E.totals x) (E.totals z) ∧
    mean E.clusterAssignmentDesign (covarianceWithZeroOmission E.clusterAssignmentDesign (E.totals x) (E.totals z)) ≤ designCovariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign true (E.totals x)) (htSum E.clusterAssignmentDesign false (E.totals z)) ∧
    (mean E.clusterAssignmentDesign (covarianceWithZeroOmission E.clusterAssignmentDesign (E.totals x) (E.totals z)) = designCovariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign true (E.totals x)) (htSum E.clusterAssignmentDesign false (E.totals z)) ↔
      ∀ i, (E.totals x) i = (E.totals z) i)) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (x z : U → ℝ),
    populationCovarianceBound E.clusterAssignmentDesign (E.totals x) (E.totals z) ≤
      designCovariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign true (E.totals x))
        (htSum E.clusterAssignmentDesign false (E.totals z)))

end
end SAP.P026a
