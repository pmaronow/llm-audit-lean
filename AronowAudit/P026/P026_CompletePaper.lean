import AronowAudit.P026.P026_PaperScope
import AronowAudit.P026.P026_IndependenceCompletion
import AronowAudit.P009.P009_FullBiasCompletion

namespace AronowAudit.P026.PaperScope
open Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000


/-- The full equal-marginal fixed-count clause of Equation[12], for any
actual cluster allocation law satisfying the stated randomization premises. -/
theorem complete_clusters_T21 {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (M m : ℕ) (hm : 0 < m) (hmM : m < M) (E : ClusterExperiment U (Fin M))
    (hmarg : ∀ i, marginal E.clusterDesign true i=(m:ℝ)/M ∧
      marginal E.clusterDesign false i=((M-m:ℕ):ℝ)/M)
    (hcount : ∀ w, 0 < E.clusterDesign.weight w → (∑i,indicator E.clusterDesign true w i)=m)
    (x z : U→ℝ) :
    (∀ w, ht E.unitDesign (Fintype.card U) x z w=(M:ℝ)/(Fintype.card U)*
      (observedArmSum E.clusterDesign true (E.totals x) (E.totals z) w/m-
       observedArmSum E.clusterDesign false (E.totals x) (E.totals z) w/(M-m:ℕ))) ∧
    expectation E.unitDesign (ht E.unitDesign (Fintype.card U) x z)=
      ate (Fintype.card U) x z := by
  have hh := complete_clusters E.clusterDesign E.cluster_probability E.cluster_marginals
    (Fintype.card U) M m Fintype.card_pos hm hmM hmarg hcount (E.totals x) (E.totals z)
  refine ⟨?_,(ht_unbiased E.unitDesign E.unit_probability E.unit_marginals
    (Fintype.card U) Fintype.card_pos x z).2.2⟩
  intro w
  change (htTotal E.unitDesign true x w-htTotal E.unitDesign false z w)/_=_
  rw [E.actual_cluster_aggregation x true w,E.actual_cluster_aggregation z false w]
  exact hh.1 w

theorem mutually_independent_leave_out_T5 {I : Type*} [Fintype I] [DecidableEq I]
    (E : UnitExperiment I) (h : mutuallyIndependentAssignments E.design) (i : I) :
    independent E.design (fun w => w i) (fittingAssignments E.design (univ.erase i)) :=
  IndependenceCompletion.mutually_independent_leave_out_completed E.design E.probability h i

theorem mutually_independent_other_blocks_T5 {I B : Type*} [Fintype I] [DecidableEq I]
    [Fintype B] [DecidableEq B] (E : UnitExperiment I) (c : I → B)
    (h : mutuallyIndependentBlocks E.design c) (i : I) :
    independent E.design (fun w => w i)
      (fittingAssignments E.design (univ.filter (fun j => c j≠c i))) :=
  IndependenceCompletion.mutually_independent_other_blocks_completed E.design E.probability c h i

end
end AronowAudit.P026.PaperScope
