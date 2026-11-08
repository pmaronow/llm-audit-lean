import SAP.P026a.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a.Bridge
open Finset
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem target1 : T1Statement := by
  refine ⟨?_, ?_⟩
  · simp only [covariance_continuation_eq, repaired_covariance_eq, linear_residual_eq]
    exact @AronowAudit.P026.asymmetricTwo_counterexample
  · simp only [covariance_continuation_eq, repaired_covariance_eq, linear_residual_eq]
    exact @AronowAudit.P026.asymmetricSix_counterexample

theorem target2 : T2Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated i j hij
    exact @AronowAudit.P026.PaperScope.disagreement_identity_T2 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated i j hij
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated i j hij
    exact @AronowAudit.P026.PaperScope.disagreement_positive_iff_T2 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated i j hij
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated x z
    exact @AronowAudit.P026.PaperScope.ht_cluster_covariance_T2 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated x z
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated x z
    exact @AronowAudit.P026.PaperScope.printed_variance_bias_T2 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated x z
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated x z
    simp only [covariance_continuation_eq, repaired_covariance_eq, linear_residual_eq]
    exact @AronowAudit.P026.PaperScope.corrected_covariance_bias_T2 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated x z
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated x z
    exact @AronowAudit.P026.PaperScope.corrected_variance_bias_T2 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated x z
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated c hs
    exact @AronowAudit.P026.PaperScope.corrected_sharp_null_T2 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated c hs
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated x z w hw
    simp only [covariance_continuation_eq, repaired_covariance_eq, linear_residual_eq]
    exact @AronowAudit.P026.PaperScope.corrected_variance_decomposition_T2 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated x z w hw
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated x z r
    exact @AronowAudit.P026.PaperScope.corrected_residual_variance_T2 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated x z r
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated x z
    exact @AronowAudit.P026.PaperScope.correctedBiasExpression_nonneg_T2 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated x z
  · exact @AronowAudit.P026.repaired_sharp_null_strict_bias
  · intro U C instFU instDU instNU instFC instDC instNC E x z r
    have hx : E.totals (fun i => x i - r i) = (fun c => E.totals x c - E.totals r c) := by
      funext c
      simp only [ClusterLaw.totals, sum_sub_distrib]
    have hz : E.totals (fun i => z i - r i) = (fun c => E.totals z c - E.totals r c) := by
      funext c
      simp only [ClusterLaw.totals, sum_sub_distrib]
    refine ⟨hx, hz, ?_⟩
    rw [hx, hz]
    funext w
    exact AronowAudit.P026.generalized_residual (toAuditCluster E).clusterDesign
      (Fintype.card U) (E.totals x) (E.totals z) (fun _ => E.totals r) w
  · exact ⟨(AronowAudit.P026.asymmetricTwo_counterexample.2.2.1 0 1 (by decide)).1,
      AronowAudit.P026.asymmetricTwo_counterexample.2.2.2.1⟩
  · obtain ⟨hv, hp, hc, _⟩ := AronowAudit.P026.repaired_sharp_null_strict_bias
    constructor
    · change AronowAudit.P026.expectation AronowAudit.P026.asymmetricSix
        (AronowAudit.P026.printedVariance AronowAudit.P026.asymmetricSix 6 _ _) -
        AronowAudit.P026.variance AronowAudit.P026.asymmetricSix
        (AronowAudit.P026.ht AronowAudit.P026.asymmetricSix 6 _ _) = _
      rw [hv, hp]
      norm_num
    · change AronowAudit.P026.expectation AronowAudit.P026.asymmetricSix
        (AronowAudit.P026.correctedVariance AronowAudit.P026.asymmetricSix 6 _ _) -
        AronowAudit.P026.variance AronowAudit.P026.asymmetricSix
        (AronowAudit.P026.ht AronowAudit.P026.asymmetricSix 6 _ _) = _
      rw [hv, hc]
      norm_num

theorem target3 : T3Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated hcross x z
    simp only [covariance_continuation_eq, repaired_covariance_eq, linear_residual_eq]
    exact @AronowAudit.P026.PaperScope.support_repair_T3 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated hcross x z
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated hc x z r
    exact @AronowAudit.P026.PaperScope.support_residual_variance_T3 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated hc x z r
  · exact @AronowAudit.P026.table_support
  · intro U C instFU instDU instNU instFC instDC instNC E x z r
    have hx : E.totals (fun i => x i - r i) = (fun c => E.totals x c - E.totals r c) := by
      funext c
      simp only [ClusterLaw.totals, sum_sub_distrib]
    have hz : E.totals (fun i => z i - r i) = (fun c => E.totals z c - E.totals r c) := by
      funext c
      simp only [ClusterLaw.totals, sum_sub_distrib]
    refine ⟨hx, hz, ?_⟩
    rw [hx, hz]
    funext w
    exact AronowAudit.P026.generalized_residual (toAuditCluster E).clusterDesign
      (Fintype.card U) (E.totals x) (E.totals z) (fun _ => E.totals r) w
  · let D : AssignmentDesign (Fin 3) (Fin 2) ℝ :=
      ⟨AronowAudit.P026.Refutations.realAsymmetricTwo.weight,
        AronowAudit.P026.Refutations.realAsymmetricTwo.treatment⟩
    have h := AronowAudit.P026.Refutations.asymmetric_real_certificate
    refine ⟨D, h.1, h.2.1, (fun i j hij => (h.2.2.1 i j hij).1), ?_⟩
    intro hs
    have hp := hs 0 1 (by decide)
    have hz : jointInclusion D true false 0 1 = 0 := h.2.2.2.1
    exact (ne_of_gt hp) hz

theorem target4 : T4Statement := by
  refine ⟨?_, ?_⟩
  · exact @AronowAudit.P026.xorSix_counterexample
  · exact @AronowAudit.P026.xorThree_counterexamples

theorem target5 : T5Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro I inst1 inst2 inst3 E Θ i J y1 y0 G P h
    exact @AronowAudit.P026.PaperScope.vector_fitting_independence_T5 I inst1 inst2 inst3 (toAuditUnit E) Θ i J y1 y0 G P h
  · intro I inst1 inst2 inst3 E Θ i J y1 y0 G P h
    exact @AronowAudit.P026.PaperScope.outcome_vector_fitting_independence_T5 I inst1 inst2 inst3 (toAuditUnit E) Θ i J y1 y0 G P h
  · intro I inst1 inst2 inst3 E x z J G h
    exact @AronowAudit.P026.PaperScope.vector_fitting_unbiased_T5 I inst1 inst2 inst3 (toAuditUnit E) x z J G h
  · intro I inst1 inst2 inst3 E i J x z a b h
    exact @AronowAudit.P026.PaperScope.additive_fitting_unbiased_T5 I inst1 inst2 inst3 (toAuditUnit E) i J x z a b h
  · intro I inst1 inst2 E h i
    exact @AronowAudit.P026.PaperScope.mutually_independent_leave_out_T5 I inst1 inst2 (toAuditUnit E) h i
  · intro I B inst2 inst3 inst4 inst5 E c h i
    exact @AronowAudit.P026.PaperScope.mutually_independent_other_blocks_T5 I B inst2 inst3 inst4 inst5 (toAuditUnit E) c h i

theorem target6 : T6Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [show (∑ i, (paperTableCenteredX i)^2) = (331/10 : ℚ) from AronowAudit.P026.fe_x_norm.1]
      exact AronowAudit.P026.fe_x_norm.2
    · intro w
      exact (AronowAudit.P026.fe_normal_equations w).1
  · exact linear_residual_eq
  · simp only [covariance_continuation_eq, repaired_covariance_eq, linear_residual_eq]
    exact @AronowAudit.P026.table_linear_moments
  · simp only [covariance_continuation_eq, repaired_covariance_eq, linear_residual_eq]
    exact @AronowAudit.P026.table_linear_refutation
  · exact @AronowAudit.P026.fe_table_moments

theorem target7 : T7Statement := by
  refine ⟨?_, ?_⟩
  · constructor
    · rw [show (∑ i, (paperTableCenteredX i)^2) = (331/10 : ℚ) from AronowAudit.P026.fe_x_norm.1]
      exact AronowAudit.P026.fe_x_norm.2
    · intro w
      exact (AronowAudit.P026.fe_normal_equations w).1
  · simp only [covariance_continuation_eq, repaired_covariance_eq, linear_residual_eq]
    exact @AronowAudit.P026.Refutations.table2_correction_T7

theorem target8 : T8Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated x z
    exact @AronowAudit.P026.PaperScope.ht_cluster_covariance_T8 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated x z
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated x z
    exact @AronowAudit.P026.PaperScope.covariance_bound_gap_T8 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated x z
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated hc x z
    simp only [covariance_continuation_eq, repaired_covariance_eq, linear_residual_eq]
    exact @AronowAudit.P026.PaperScope.appendixE_corrected_T8 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated hc x z
  · intro U C instFU instDU instNU instFC instDC instNC E hseparated x z
    have hg := AronowAudit.P026.PaperScope.covariance_bound_gap_T8
      (toAuditCluster E) hseparated x z
    have hn : 0 ≤ ∑ c, (E.totals x c - E.totals z c)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
    change designCovariance E.clusterAssignmentDesign
      (htSum E.clusterAssignmentDesign true (E.totals x))
      (htSum E.clusterAssignmentDesign false (E.totals z)) -
      populationCovarianceBound E.clusterAssignmentDesign (E.totals x) (E.totals z) =
        (∑ c, (E.totals x c - E.totals z c)^2) / 2 at hg
    linarith

theorem target9 : T9Statement := by
  refine ⟨?_, ?_⟩
  · simp only [covariance_continuation_eq, repaired_covariance_eq, linear_residual_eq]
    exact @AronowAudit.P026.appendixE_counterexample
  · obtain ⟨hprob, hpos, hs, hj, hvalues, he, hcov, hpop, hprinted, hvar, hne⟩ :=
      AronowAudit.P026.appendixE_counterexample
    have hg := AronowAudit.P026.covariance_bound_gap AronowAudit.P026.twoOfFour hpos
      AronowAudit.P026.appendixOutcomes AronowAudit.P026.appendixOutcomes
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sum_const_zero, zero_div] at hg
    change AronowAudit.P026.covarianceBound AronowAudit.P026.twoOfFour
      AronowAudit.P026.appendixOutcomes AronowAudit.P026.appendixOutcomes = _
    linarith

theorem target10 : T10Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro U C inst2 inst3 inst4 inst5 inst6 E y a w
    exact @AronowAudit.P026.PaperScope.cluster_aggregation_T10 U C inst2 inst3 inst4 inst5 inst6 (toAuditCluster E) y a w
  · intro U C instFU instDU instNU instFC instDC E x z w
    change (htSum E.unitAssignmentDesign true x w - htSum E.unitAssignmentDesign false z w) / _ = _
    change _ = (htSum E.clusterAssignmentDesign true (E.totals x) w -
      htSum E.clusterAssignmentDesign false (E.totals z) w) / _
    rw [show htSum E.unitAssignmentDesign true x w =
      htSum E.clusterAssignmentDesign true (E.totals x) w from
        AronowAudit.P026.PaperScope.cluster_aggregation_T10 (toAuditCluster E) x true w,
      show htSum E.unitAssignmentDesign false z w =
      htSum E.clusterAssignmentDesign false (E.totals z) w from
        AronowAudit.P026.PaperScope.cluster_aggregation_T10 (toAuditCluster E) z false w]
  · intro U C instFU instDU instNU instFC instDC E y a w
    dsimp only
    have hgroup :
        (∑ c, ∑ i ∈ univ.filter (fun i => E.cluster i = c),
          armIndicator E.unitAssignmentDesign a w i * y i / inclusion E.unitAssignmentDesign a i) =
        ∑ c, ∑ i ∈ univ.filter (fun i => E.cluster i = c),
          armIndicator E.clusterAssignmentDesign a w c * y i / inclusion E.clusterAssignmentDesign a c := by
      apply sum_congr rfl
      intro c hc
      apply sum_congr rfl
      intro i hi
      have hm : E.cluster i = c := (mem_filter.mp hi).2
      subst c
      rfl
    have hfactor :
        (∑ c, ∑ i ∈ univ.filter (fun i => E.cluster i = c),
          armIndicator E.clusterAssignmentDesign a w c * y i / inclusion E.clusterAssignmentDesign a c) =
        ∑ c, armIndicator E.clusterAssignmentDesign a w c *
          (∑ i ∈ univ.filter (fun i => E.cluster i = c), y i) / inclusion E.clusterAssignmentDesign a c := by
      simp only [mul_sum, sum_div]
    refine ⟨?_, hgroup, hfactor, rfl⟩
    exact (show htSum E.unitAssignmentDesign a y w =
      htSum E.clusterAssignmentDesign a (E.totals y) w from
      AronowAudit.P026.PaperScope.cluster_aggregation_T10 (toAuditCluster E) y a w).trans
        (hgroup.trans hfactor).symm

theorem target11 : T11Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated a y
    exact @AronowAudit.P026.PaperScope.ht_arm_variance_T11 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated a y
  · intro U C inst2 inst3 inst4 inst5 inst6 inst7 E hseparated a x z
    exact @AronowAudit.P026.PaperScope.arm_variance_corrected_T11 U C inst2 inst3 inst4 inst5 inst6 inst7 (toAuditCluster E) hseparated a x z
  · intro U C instFU instDU instNU instFC instDC instNC E hseparated a x z hs
    rw [← full_support_arm_eq E.clusterAssignmentDesign a (E.totals x) (E.totals z) hs]
    exact (AronowAudit.P026.PaperScope.arm_variance_corrected_T11
      (toAuditCluster E) hseparated a x z).2.2.2 hs

end
end SAP.P026a.Bridge
