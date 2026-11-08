import AronowAudit.P026.P026_PaperScope
import AronowAudit.P026.P026_IndependenceCompletion
import AronowAudit.P009.P009_FullBiasCompletion

namespace AronowAudit.P026.PaperScope
open Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000

def completeAssignment (M m : ℕ) (hm : 0 < m) (hmM : m < M) : UnitExperiment (Fin M) where
  weight := (P009.FullBiasCompletion.completeLaw M m hmM.le).mass
  nonnegative := (P009.FullBiasCompletion.completeLaw M m hmM.le).nonneg
  normalized := (P009.FullBiasCompletion.completeLaw M m hmM.le).total
  positive := by
    intro i
    let F := P009.FullBiasCompletion.completeExperiment M m hmM.le (fun _ _ => 0)
    have hF : P009.Complete F m := P009.FullBiasCompletion.complete_certificate M m hm hmM _
    have ht := P009.CompleteConditional.complete_marginal_true F m hF i
    have hf := P009.CompleteConditional.complete_marginal_false F m hF i
    change (∑ w, F.design.mass w * (if w i=true then 1 else 0)) > 0 ∧
      (∑ w, F.design.mass w * (if w i=false then 1 else 0)) > 0
    simp only [P009.marginal,P009.prob,P009.mean] at ht hf
    rw [show (∑ w, F.design.mass w * (if w i=true then 1 else 0))=(m:ℝ)/M from by simpa using ht,
      show (∑ w, F.design.mass w * (if w i=false then 1 else 0))=1-(m:ℝ)/M from by simpa using hf]
    have hM : (0:ℝ) < M := by exact_mod_cast (hm.trans hmM)
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    have hmM' : (m:ℝ) < M := by exact_mod_cast hmM
    exact ⟨div_pos hm' hM,sub_pos.mpr ((div_lt_one hM).mpr hmM')⟩

lemma completeAssignment_marginals (M m : ℕ) (hm : 0 < m) (hmM : m < M) (i : Fin M) :
    marginal (completeAssignment M m hm hmM).design true i = (m:ℝ)/M ∧
    marginal (completeAssignment M m hm hmM).design false i = ((M-m:ℕ):ℝ)/M := by
  let F := P009.FullBiasCompletion.completeExperiment M m hmM.le (fun _ _ => 0)
  have hF : P009.Complete F m := P009.FullBiasCompletion.complete_certificate M m hm hmM _
  have ht := P009.CompleteConditional.complete_marginal_true F m hF i
  have hf := P009.CompleteConditional.complete_marginal_false F m hF i
  constructor
  · change (∑ w, (P009.FullBiasCompletion.completeLaw M m hmM.le).mass w * (if w i=true then 1 else 0))=_
    simp_rw [mul_ite,mul_one,mul_zero]
    simpa [P009.marginal,P009.prob,P009.mean,P009.FullBiasCompletion.completeExperiment,F] using ht
  · have hff : marginal (completeAssignment M m hm hmM).design false i=1-(m:ℝ)/M := by
      change (∑ w, (P009.FullBiasCompletion.completeLaw M m hmM.le).mass w * (if w i=false then 1 else 0))=_
      simp_rw [mul_ite,mul_one,mul_zero]
      simpa [P009.marginal,P009.prob,P009.mean,P009.FullBiasCompletion.completeExperiment,F] using hf
    rw [hff,Nat.cast_sub hmM.le]
    have hM : (M:ℝ)≠0 := by exact_mod_cast (hm.trans hmM).ne'
    field_simp

lemma completeAssignment_count (M m : ℕ) (hm : 0 < m) (hmM : m < M)
    (w : Fin M → Bool) (hw : 0 < (completeAssignment M m hm hmM).weight w) :
    (∑ i, indicator (completeAssignment M m hm hmM).design true w i) = m := by
  let F := P009.FullBiasCompletion.completeExperiment M m hmM.le (fun _ _ => 0)
  have hF : P009.Complete F m := P009.FullBiasCompletion.complete_certificate M m hm hmM _
  have hh := P009.CompleteConditional.supported_treated_count F m hF w hw
  change (∑ i, if w i=true then (1:ℝ) else 0)=m
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hw : w i <;> simp [P009.bit,hw]

/-- Equation [12] for literal uniform m-of-M cluster assignment and a fixed
unit partition. Both normalization factors are the actual population counts. -/
theorem complete_clusters_uniform_instance {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (M m : ℕ) (hm : 0 < m) (hmM : m < M) (c : U → Fin M) (hc : Function.Surjective c)
    (x z : U → ℝ) :
    let E : ClusterExperiment U (Fin M) := ⟨c,hc,completeAssignment M m hm hmM⟩
    (∀ w, ht E.unitDesign (Fintype.card U) x z w = (M:ℝ)/(Fintype.card U) *
      (observedArmSum E.clusterDesign true (E.totals x) (E.totals z) w/m-
       observedArmSum E.clusterDesign false (E.totals x) (E.totals z) w/(M-m:ℕ))) ∧
    expectation E.unitDesign (ht E.unitDesign (Fintype.card U) x z) =
      ate (Fintype.card U) x z := by
  let E : ClusterExperiment U (Fin M) := ⟨c,hc,completeAssignment M m hm hmM⟩
  have hh := complete_clusters E.clusterDesign E.cluster_probability E.cluster_marginals
    (Fintype.card U) M m Fintype.card_pos hm hmM
    (completeAssignment_marginals M m hm hmM) (completeAssignment_count M m hm hmM)
    (E.totals x) (E.totals z)
  refine ⟨?_, (ht_unbiased E.unitDesign E.unit_probability E.unit_marginals
    (Fintype.card U) Fintype.card_pos x z).2.2⟩
  intro w
  change (htTotal E.unitDesign true x w-htTotal E.unitDesign false z w)/_ = _
  rw [E.actual_cluster_aggregation x true w,E.actual_cluster_aggregation z false w]
  exact hh.1 w

/-- The full equal-marginal fixed-count clause of Equation[12], for any
actual cluster allocation law satisfying the stated randomization premises.
The uniform m-of-M construction above is a certified special case. -/
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

#print axioms complete_clusters_uniform_instance
#print axioms complete_clusters_T21
#print axioms mutually_independent_leave_out_T5
#print axioms mutually_independent_other_blocks_T5
end
end AronowAudit.P026.PaperScope
