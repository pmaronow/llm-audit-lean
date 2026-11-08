import SAP.P026a.Defs
import AronowAudit.P026.P026_CompletePaper
import AronowAudit.P026.P026_Refutations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a.Bridge
open Finset
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Preserve the assignment weights and indicators exactly. -/
def toAuditDesign {Ω I R : Type*} (D : AssignmentDesign Ω I R) :
    AronowAudit.P026.Design Ω I R := ⟨D.weight, D.treatment⟩

def toAuditUnit {I : Type*} [Fintype I] [DecidableEq I] (E : UnitLaw I) :
    AronowAudit.P026.PaperScope.UnitExperiment I :=
  ⟨E.weight, E.nonnegative, E.normalized, E.positive⟩

def toAuditCluster {U C : Type*} [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] (E : ClusterLaw U C) :
    AronowAudit.P026.PaperScope.ClusterExperiment U C :=
  ⟨E.cluster, E.covers, toAuditUnit E.assignment⟩

theorem unit_design_eq {I : Type*} [Fintype I] [DecidableEq I] (E : UnitLaw I) :
    (toAuditUnit E).design = toAuditDesign E.assignmentDesign := rfl

theorem cluster_design_eq {U C : Type*} [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] (E : ClusterLaw U C) :
    (toAuditCluster E).clusterDesign = toAuditDesign E.clusterAssignmentDesign := rfl

theorem unit_cluster_design_eq {U C : Type*} [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] (E : ClusterLaw U C) :
    (toAuditCluster E).unitDesign = toAuditDesign E.unitAssignmentDesign := rfl

theorem cluster_totals_eq {U C : Type*} [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] (E : ClusterLaw U C) (y : U → ℝ) :
    (toAuditCluster E).totals y = E.totals y := rfl

/-- The guarded SAP continuation agrees with the project's total field formula. -/
theorem covariance_continuation_eq {Ω I R : Type*} [Fintype Ω] [Fintype I]
    [DecidableEq I] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (D : AssignmentDesign Ω I R) (x z : I → R) :
    covarianceWithZeroOmission D x z =
      AronowAudit.P026.printedCovariance (toAuditDesign D) x z := by
  funext w
  unfold covarianceWithZeroOmission AronowAudit.P026.printedCovariance
  change orderedOffDiagonalSum (fun i j => if jointInclusion D true false i j = 0 then 0 else
    armIndicator D true w i * armIndicator D false w j / jointInclusion D true false i j *
    (jointInclusion D true false i j - inclusion D true i * inclusion D false j) *
    (response D x z w i / inclusion D true i) * (response D x z w j / inclusion D false j)) - _ - _ = _
  have pair_guard (i j : I) :
      (if jointInclusion D true false i j = 0 then (0 : R) else
        armIndicator D true w i * armIndicator D false w j / jointInclusion D true false i j *
        (jointInclusion D true false i j - inclusion D true i * inclusion D false j) *
        (response D x z w i / inclusion D true i) * (response D x z w j / inclusion D false j)) =
        armIndicator D true w i * armIndicator D false w j / jointInclusion D true false i j *
        (jointInclusion D true false i j - inclusion D true i * inclusion D false j) *
        (response D x z w i / inclusion D true i) * (response D x z w j / inclusion D false j) := by
    split_ifs with h
    · simp [h]
    · rfl
  simp only [pair_guard]
  rfl

theorem repaired_covariance_eq {Ω I R : Type*} [Fintype Ω] [Fintype I]
    [DecidableEq I] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (D : AssignmentDesign Ω I R) (x z : I → R) :
    repairedCovarianceEstimate D x z =
      AronowAudit.P026.correctedCovariance (toAuditDesign D) x z := by
  funext w
  unfold repairedCovarianceEstimate AronowAudit.P026.correctedCovariance
  rw [covariance_continuation_eq]
  rfl

/-- Transport the already exported calculation of the actual residual cluster sums. -/
theorem linear_residual_eq : paperTableLinearResidual = AronowAudit.P026.tableLinearResidual := by
  funext k
  exact AronowAudit.P026.table_linear_fits.2.2.2.2.2.2 k

/-- Under full support the corrected arm formula reduces to the literal equation [31]. -/
theorem full_support_arm_eq {Ω I R : Type*} [Fintype Ω] [Fintype I]
    [DecidableEq I] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (D : AssignmentDesign Ω I R) (a : Bool) (x z : I → R)
    (hs : ∀ i j, i ≠ j → 0 < jointInclusion D a a i j) :
    armVarianceEstimate D a x z = fullSupportArmEstimate D a x z := by
  funext w
  unfold armVarianceEstimate fullSupportArmEstimate
  have hz : unavailablePairSum D a a (fun i j =>
      armIndicator D a w i * response D x z w i ^ 2 / (2 * inclusion D a i) +
      armIndicator D a w j * response D x z w j ^ 2 / (2 * inclusion D a j)) = 0 :=
    AronowAudit.P026.VarianceCompletion.zeroSum_of_positive (toAuditDesign D) a a hs _
  rw [hz, add_zero]
  congr 1
  unfold orderedOffDiagonalSum
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  have hp := hs i j (mem_erase.mp hj).1.symm
  simp only [if_pos hp, estimatedPairTerm, zeroAdjustment, if_neg (ne_of_gt hp), add_zero]

end
end SAP.P026a.Bridge
