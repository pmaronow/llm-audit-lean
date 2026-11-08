import SAP.P033.Defs
import SAP.P033.Bridge
import AronowAudit.P010.Wave1.Gap.GP010P033B1b
import AronowAudit.P010.Wave1.Gap.GP010P033B2
import AronowAudit.P033.P033_Audit
import AronowAudit.P033.Wave1.Gap.GLP010P033P033B1
import AronowAudit.P033.Wave1.Gap.GLP010P033P033B2
import AronowAudit.P033.Wave1.Gap.GLP010P033P033B3
import SAP.P033.WH.W1.Proofs.T1
import SAP.P033.WH.W1.Proofs.T2
import SAP.P033.WH.W1.Proofs.T4
import SAP.P033.WH.W1.Proofs.T5

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

theorem SAP.P033.T1 : SAP.P033.T1WholeStatement := SAP.P033.WH.W1.T1_whole

theorem SAP.P033.T2 : SAP.P033.T2WholeStatement := SAP.P033.WH.W1.T2_whole

theorem SAP.P033.T3 : SAP.P033.T3Statement := by
  have hcore := SAP.P033.Bridge.T3_correspondence.mpr
    AronowAudit.P033.clustered_variance_counterexample
  refine ⟨hcore,
    SAP.P033.Bridge.ClusterCertificate_correspondence.mpr
      AronowAudit.P033.cluster_exact_certificate,
    SAP.P033.Bridge.ClusterWLSCertificate_correspondence.mpr
      AronowAudit.P033.cluster_wls_rows, ?_, ?_⟩
  · intro ω g
    have hz := AronowAudit.P033.nn_residual_sum (by norm_num : 2 ≤ 5)
      (AronowAudit.P033.noisyClusterOutcome ω g)
    change (AronowAudit.P033.clusterLinear g/5)*
      (∑ i, AronowAudit.P033.nnResidual (AronowAudit.P033.noisyClusterOutcome ω g) i) = 0 ∧
      (AronowAudit.P033.clusterCorrected g/5)*
      (∑ i, AronowAudit.P033.nnResidual (AronowAudit.P033.noisyClusterOutcome ω g) i) = 0
    simp [hz]
  · intro f
    have ha (ω : Fin 10 → Bool) : SAP.P033.clusterScoreVariance f
        (fun g => (SAP.P033.clusterLinear g/5)*∑ i, SAP.P033.nnResidual
          (SAP.P033.clusterOutcome ω g) i) = 0 :=
      (AronowAudit.P033.clustered_zero_vs_positive.2.2.2.2 f
        (AronowAudit.P033.clusterOutcome ω)).1
    have hb (ω : Fin 10 → Bool) : SAP.P033.clusterScoreVariance f
        (fun g => (SAP.P033.clusterCorrected g/5)*∑ i, SAP.P033.nnResidual
          (SAP.P033.clusterOutcome ω g) i) = 0 :=
      (AronowAudit.P033.clustered_zero_vs_positive.2.2.2.2 f
        (AronowAudit.P033.clusterOutcome ω)).2
    constructor
    · convert hcore.2.2.2.2.2.2.2.2.2.2.2.2.1 using 1
      congr 1
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ha,
        Real.sqrt_zero, mul_zero, sub_zero, add_zero, Icc_self, mem_singleton_iff, eq_comm]
    · convert hcore.2.2.2.2.2.2.2.2.2.2.2.2.2.1 using 1
      congr 1
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hb,
        Real.sqrt_zero, mul_zero, sub_zero, add_zero, Icc_self, mem_singleton_iff, eq_comm]

theorem SAP.P033.T4 : SAP.P033.T4WholeStatement := SAP.P033.WH.W1.T4_whole

theorem SAP.P033.T5 : SAP.P033.T5WholeStatement := SAP.P033.WH.W1.T5_whole

theorem SAP.P033.T6 : SAP.P033.T6Statement := by
  exact SAP.P033.Bridge.T6_correspondence.mpr
    (@AronowAudit.P033.Wave1.binary_standardization_correction_proof)

theorem SAP.P033.T7 : SAP.P033.T7Statement := by
  refine ⟨SAP.P033.Bridge.T7_correspondence.mpr
    AronowAudit.P033.Wave1.caliper_counterexamples_proof, ?_, ?_, ?_,
    SAP.P033.Bridge.linear_count_positive⟩
  · exact AronowAudit.P033.caliper_exact_tails.2.2.2.2.2.2.1
  · exact AronowAudit.P033.caliper_exact_tails.2.2.2.2.2.2.2.1
  · exact AronowAudit.P033.caliper_exact_tails.2.2.2.2.2.2.2.2.1

theorem SAP.P033.T8 : SAP.P033.T8Statement := by
  refine ⟨SAP.P033.Bridge.T8_correspondence.mpr
    (@AronowAudit.P033.Wave1.caliper_correction_proof), ?_⟩
  intro M h hh X
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_Icc] at hi ⊢
  exact ⟨by linarith [hi.1], hi.2⟩

theorem SAP.P033.T9 : SAP.P033.T9Statement := by
  exact ⟨SAP.P033.Bridge.T9_correspondence.mpr
    (@AronowAudit.P033.Wave1.native_power_correction_proof),
    by norm_num, by norm_num⟩

theorem SAP.P033.T10 : SAP.P033.T10Statement := by
  exact ⟨SAP.P033.Bridge.T10_correspondence.mpr
    AronowAudit.P033.funnel_counterexample, by norm_num⟩

theorem SAP.P033.T11 : SAP.P033.T11Statement := by
  have hz := AronowAudit.P033.Wave1.pseudo_counter_quantile_bounds
  have hp := AronowAudit.P033.Wave1.GP010P033B1b_t1_critical_pos
  refine ⟨SAP.P033.Bridge.T11_correspondence.mpr
    AronowAudit.P033.funnel_correction, hp, ?_, ?_⟩
  · change (51021/10^5 : ℝ) < 1/AronowAudit.P033.normalCritical
    apply (lt_div_iff₀ hp).2
    nlinarith only [hz.2.1]
  · change 1/AronowAudit.P033.normalCritical < (51022/10^5 : ℝ)
    apply (div_lt_iff₀ hp).2
    nlinarith only [hz.1]

theorem SAP.P033.T12 : SAP.P033.T12Statement := by
  exact SAP.P033.Bridge.T12_correspondence.mpr
    (@AronowAudit.P033.Wave1.pseudo_p_counterexample_proof)

theorem SAP.P033.T13 : SAP.P033.T13Statement := by
  exact SAP.P033.Bridge.T13_correspondence.mpr
    (@AronowAudit.P033.Wave1.pseudo_p_correction_proof)

theorem SAP.P033.T14 : SAP.P033.T14Statement := by
  exact SAP.P033.Bridge.T14_correspondence.mpr
    (@AronowAudit.P033.interval_rule_counterexample)

theorem SAP.P033.T15 : SAP.P033.T15Statement := by
  exact SAP.P033.Bridge.T15_correspondence.mpr
    (@AronowAudit.P033.interval_rule_correction)

