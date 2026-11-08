import SAP.P026a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section


/-- Mathematical content of target P026-T2. -/
def T2Statement : Prop :=
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (i j :  C)
    (hij : i ≠ j),
    disagreementProbability E.clusterAssignmentDesign i j = jointInclusion E.clusterAssignmentDesign true false i j + jointInclusion E.clusterAssignmentDesign true false j i) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (i j :  C)
    (hij : i ≠ j),
    0 < disagreementProbability E.clusterAssignmentDesign i j ↔
      0 < jointInclusion E.clusterAssignmentDesign true false i j ∨ 0 < jointInclusion E.clusterAssignmentDesign true false j i) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (x z : U → ℝ),
    designCovariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign true (E.totals x)) (htSum E.clusterAssignmentDesign false (E.totals z)) =
      populationCrossCovariance E.clusterAssignmentDesign (E.totals x) (E.totals z)) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (x z : U → ℝ),
    ((Fintype.card U) : ℝ)^2 * (mean E.clusterAssignmentDesign (printedVarianceEstimate E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z)) - designVariance E.clusterAssignmentDesign (htContrast E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z))) =
      (∑ i, ((E.totals x) i-(E.totals z) i)^2) + unavailablePairSum E.clusterAssignmentDesign true true (fun i j => ((E.totals x) i+(E.totals x) j)^2) / 2 +
      unavailablePairSum E.clusterAssignmentDesign false false (fun i j => ((E.totals z) i+(E.totals z) j)^2) / 2 -
      2 * unavailablePairSum E.clusterAssignmentDesign true false (fun i j => (E.totals x) i*(E.totals z) j)) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (x z : U → ℝ),
    mean E.clusterAssignmentDesign (repairedCovarianceEstimate E.clusterAssignmentDesign (E.totals x) (E.totals z)) -
      designCovariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign true (E.totals x)) (htSum E.clusterAssignmentDesign false (E.totals z)) =
      -(∑ i, ((E.totals x) i-(E.totals z) i)^2) / 2 - unavailablePairSum E.clusterAssignmentDesign true false (fun i j => ((E.totals x) i-(E.totals z) j)^2) / 2 ∧
    mean E.clusterAssignmentDesign (repairedCovarianceEstimate E.clusterAssignmentDesign (E.totals x) (E.totals z)) ≤
      designCovariance E.clusterAssignmentDesign (htSum E.clusterAssignmentDesign true (E.totals x)) (htSum E.clusterAssignmentDesign false (E.totals z))) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (x z : U → ℝ),
    ((Fintype.card U) : ℝ)^2 * (mean E.clusterAssignmentDesign (repairedVarianceEstimate E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z)) - designVariance E.clusterAssignmentDesign (htContrast E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z))) =
      repairedBias E.clusterAssignmentDesign (E.totals x) (E.totals z) ∧
    designVariance E.clusterAssignmentDesign (htContrast E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z)) ≤ mean E.clusterAssignmentDesign (repairedVarianceEstimate E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z))) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (c : U → ℝ)
    (hs :  ∀ i j, i ≠ j → 0 < jointInclusion E.clusterAssignmentDesign true true i j ∧ 0 < jointInclusion E.clusterAssignmentDesign false false i j),
    mean E.clusterAssignmentDesign (repairedVarianceEstimate E.clusterAssignmentDesign (Fintype.card U) (E.totals c) (E.totals c)) - designVariance E.clusterAssignmentDesign (htContrast E.clusterAssignmentDesign (Fintype.card U) (E.totals c) (E.totals c)) =
      unavailablePairSum E.clusterAssignmentDesign true false (fun i j => ((E.totals c) i-(E.totals c) j)^2) / ((Fintype.card U) : ℝ)^2 ∧
    (mean E.clusterAssignmentDesign (repairedVarianceEstimate E.clusterAssignmentDesign (Fintype.card U) (E.totals c) (E.totals c)) = designVariance E.clusterAssignmentDesign (htContrast E.clusterAssignmentDesign (Fintype.card U) (E.totals c) (E.totals c)) ↔
      ∀ i j, i ≠ j → jointInclusion E.clusterAssignmentDesign true false i j = 0 → (E.totals c) i = (E.totals c) j)) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (x z : U → ℝ)
    (w :  (C → Bool))
    (hw :  0 < E.clusterAssignmentDesign.weight w),
    repairedVarianceEstimate E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z) w=(armVarianceEstimate E.clusterAssignmentDesign true (E.totals x) (E.totals z) w+
      armVarianceEstimate E.clusterAssignmentDesign false (E.totals x) (E.totals z) w-2*repairedCovarianceEstimate E.clusterAssignmentDesign (E.totals x) (E.totals z) w)/((Fintype.card U) : ℝ)^2) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (x z r : U → ℝ),
    ((Fintype.card U) : ℝ)^2 * (mean E.clusterAssignmentDesign (repairedVarianceEstimate E.clusterAssignmentDesign (Fintype.card U) (fun i => (E.totals x) i-(E.totals r) i) (fun i => (E.totals z) i-(E.totals r) i))-
      designVariance E.clusterAssignmentDesign (adjustedContrast E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z) (fun _ => (E.totals r)))) =
        repairedBias E.clusterAssignmentDesign (fun i => (E.totals x) i-(E.totals r) i) (fun i => (E.totals z) i-(E.totals r) i) ∧
    designVariance E.clusterAssignmentDesign (adjustedContrast E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z) (fun _ => (E.totals r))) ≤
      mean E.clusterAssignmentDesign (repairedVarianceEstimate E.clusterAssignmentDesign (Fintype.card U) (fun i => (E.totals x) i-(E.totals r) i) (fun i => (E.totals z) i-(E.totals r) i))) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreementProbability E.clusterAssignmentDesign c d)
    (x z : U → ℝ),
    0 ≤ repairedBias E.clusterAssignmentDesign (E.totals x) (E.totals z)) ∧
  (designVariance asymmetricSixLaw (htContrast asymmetricSixLaw 6 (![1,2,1,1,1,1]) (![1,2,1,1,1,1])) = 2759/12600 ∧
    mean asymmetricSixLaw (printedVarianceEstimate asymmetricSixLaw 6 (![1,2,1,1,1,1]) (![1,2,1,1,1,1])) = 151/1400 ∧
    mean asymmetricSixLaw (repairedVarianceEstimate asymmetricSixLaw 6 (![1,2,1,1,1,1]) (![1,2,1,1,1,1])) = 3109/12600 ∧
    (2759/12600 : ℚ) < 3109/12600) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterLaw U C) (x z r : U → ℝ),
    E.totals (fun i => x i - r i) = (fun c => E.totals x c - E.totals r c) ∧
    E.totals (fun i => z i - r i) = (fun c => E.totals z c - E.totals r c) ∧
    adjustedContrast E.clusterAssignmentDesign (Fintype.card U)
      (E.totals x) (E.totals z) (fun _ => E.totals r) =
    htContrast E.clusterAssignmentDesign (Fintype.card U)
      (E.totals (fun i => x i - r i)) (E.totals (fun i => z i - r i))) ∧
  (0 < disagreementProbability asymmetricPairLaw 0 1 ∧
    jointInclusion asymmetricPairLaw true false 0 1 = 0) ∧
  (mean asymmetricSixLaw
      (printedVarianceEstimate asymmetricSixLaw 6 ![1,2,1,1,1,1] ![1,2,1,1,1,1]) -
    designVariance asymmetricSixLaw (htContrast asymmetricSixLaw 6 ![1,2,1,1,1,1] ![1,2,1,1,1,1]) = -1/9 ∧
    mean asymmetricSixLaw
      (repairedVarianceEstimate asymmetricSixLaw 6 ![1,2,1,1,1,1] ![1,2,1,1,1,1]) -
    designVariance asymmetricSixLaw (htContrast asymmetricSixLaw 6 ![1,2,1,1,1,1] ![1,2,1,1,1,1]) = 1/36)

end
end SAP.P026a
