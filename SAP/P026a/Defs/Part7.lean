import SAP.P026a.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section


/-- Mathematical content of target P026-T3. -/
def T3Statement : Prop :=
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (hcross :  directedSupport E.clusterAssignmentDesign)
    (x z : U → ℝ),
    mean E.clusterAssignmentDesign (covarianceWithZeroOmission E.clusterAssignmentDesign (E.totals x) (E.totals z)) - designCovariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign true (E.totals x)) (htSum E.clusterAssignmentDesign false (E.totals z)) =
      -(∑ i, ((E.totals x) i-(E.totals z) i)^2) / 2 ∧
    mean E.clusterAssignmentDesign (covarianceWithZeroOmission E.clusterAssignmentDesign (E.totals x) (E.totals z)) ≤ designCovariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign true (E.totals x)) (htSum E.clusterAssignmentDesign false (E.totals z)) ∧
    ((Fintype.card U) : ℝ)^2 * (mean E.clusterAssignmentDesign (printedVarianceEstimate E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z)) - designVariance E.clusterAssignmentDesign (htContrast E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z))) =
      (∑ i, ((E.totals x) i-(E.totals z) i)^2) + unavailablePairSum E.clusterAssignmentDesign true true (fun i j => ((E.totals x) i+(E.totals x) j)^2) / 2 +
        unavailablePairSum E.clusterAssignmentDesign false false (fun i j => ((E.totals z) i+(E.totals z) j)^2) / 2 ∧
    designVariance E.clusterAssignmentDesign (htContrast E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z)) ≤ mean E.clusterAssignmentDesign (printedVarianceEstimate E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z)) ∧
    ((∀ i, (E.totals x) i = (E.totals z) i) →
      (∀ i j, i ≠ j → 0 < jointInclusion E.clusterAssignmentDesign true true i j ∧ 0 < jointInclusion E.clusterAssignmentDesign false false i j) →
      mean E.clusterAssignmentDesign (printedVarianceEstimate E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z)) = designVariance E.clusterAssignmentDesign (htContrast E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z)))) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (hc :  directedSupport E.clusterAssignmentDesign)
    (x z r : U → ℝ),
    designVariance E.clusterAssignmentDesign (adjustedContrast E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z) (fun _ => (E.totals r))) ≤
      mean E.clusterAssignmentDesign (printedVarianceEstimate E.clusterAssignmentDesign (Fintype.card U) (fun i => (E.totals x) i-(E.totals r) i) (fun i => (E.totals z) i-(E.totals r) i)) ∧
    ((∀ i, (E.totals x) i=(E.totals z) i) → (∀ i j, i ≠ j → 0 < jointInclusion E.clusterAssignmentDesign true true i j ∧ 0 < jointInclusion E.clusterAssignmentDesign false false i j) →
      mean E.clusterAssignmentDesign (printedVarianceEstimate E.clusterAssignmentDesign (Fintype.card U) (fun i => (E.totals x) i-(E.totals r) i) (fun i => (E.totals z) i-(E.totals r) i))=
        designVariance E.clusterAssignmentDesign (adjustedContrast E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z) (fun _ => (E.totals r))))) ∧
  (isProbability paperTableDesign ∧ hasPositiveMarginals paperTableDesign ∧
    directedSupport paperTableDesign ∧
    (∀ i j : Fin 10, i ≠ j → 1/6 ≤ jointInclusion paperTableDesign true false i j ∧
      1/15 ≤ jointInclusion paperTableDesign true true i j ∧ 1/6 ≤ jointInclusion paperTableDesign false false i j ∧
      0 < disagreementProbability paperTableDesign i j) ∧
    (∃ i j : Fin 10, i ≠ j ∧ jointInclusion paperTableDesign true false i j=1/6) ∧
    (∃ i j : Fin 10, i ≠ j ∧ jointInclusion paperTableDesign true true i j=1/15) ∧
    (∃ i j : Fin 10, i ≠ j ∧ jointInclusion paperTableDesign false false i j=1/6)) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C) (x z r : U → ℝ),
    E.totals (fun i => x i - r i) = (fun c => E.totals x c - E.totals r c) ∧
    E.totals (fun i => z i - r i) = (fun c => E.totals z c - E.totals r c) ∧
    adjustedContrast E.clusterAssignmentDesign (Fintype.card U)
      (E.totals x) (E.totals z) (fun _ => E.totals r) =
    htContrast E.clusterAssignmentDesign (Fintype.card U)
      (E.totals (fun i => x i - r i)) (E.totals (fun i => z i - r i))) ∧
  (∃ D : AssignmentDesign (Fin 3) (Fin 2) ℝ,
    isProbability D ∧ hasPositiveMarginals D ∧
    (∀ i j, i ≠ j → 0 < disagreementProbability D i j) ∧ ¬ directedSupport D)

end
end SAP.P026a
