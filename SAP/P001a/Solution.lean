import SAP.P001a.Defs
import SAP.P001a.Bridge
import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.Wave1.Gap.GLP0011B1
import AronowAudit.P001.Wave1.Gap.GLP0012B2
import AronowAudit.P001.Wave1.Gap.GLP0012B4
import AronowAudit.P001.Wave1.Gap.GP0011B1
import AronowAudit.P001.Wave1.Gap.GP0011B2
import AronowAudit.P001.Wave1.Gap.GP0012B1
import AronowAudit.P001.Wave1.Gap.GP0012B2b
import AronowAudit.P001.Wave1.Gap.GP0013B1
import AronowAudit.P001.Wave1.Gap.GP0013B1c
import AronowAudit.P001.Wave1.Gap.GP0014B2
import AronowAudit.P001.Wave1.Gap.RepairT3
import AronowAudit.P001.Wave1.Gap.TailA.HotDeckL2
import AronowAudit.P001.Wave1.Gap.TailA.MatchingFinals
import AronowAudit.P001.Wave1.Gap.TailBRegularEfficiency
import AronowAudit.P001.Wave1.Gap.TailBSieveEscape
import AronowAudit.P001.Wave1.Gap.TailBStableGram
import AronowAudit.P001.Wave1.Gap.WLP001bB2
import AronowAudit.P001.Wave1.Gap.WLP001dB1
import AronowAudit.P001.Wave1.Gap.WP001dB1
import AronowAudit.P001.Wave1.Gap.WP001dB2
import AronowAudit.P001.Wave1.UnusedMixtureMle
import SAP.P001a.WH.W1.Proofs.T18
import SAP.P001a.WH.W1.Proofs.T4
import SAP.P001a.WH.W1.Proofs.T6
import SAP.P001a.WH.W1.Proofs.T8
import SAP.P001a.WH.W2.Proofs.T12
import SAP.P001a.WH.W2.Proofs.T17
import SAP.P001a.WH.W3.Proofs.T5
import SAP.P001a.WH.W4.Proofs.T5W4

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

universe u1 u2 u3 u4 u5 u6 u7 u8

theorem SAP.P001a.T1 : SAP.P001a.T1Statement := by
  apply SAP.P001a.Bridge.T1_correspondence.mpr
  exact @AronowAudit.P001.Wave1.geometric_mean_perturbation_proof

theorem SAP.P001a.T2 : SAP.P001a.T2Statement.{u1} := by
  apply SAP.P001a.Bridge.T2_correspondence.mpr
  exact ⟨@AronowAudit.P001.sample_mean_clt_correction, SAP.P001a.T1⟩

theorem SAP.P001a.T3 : SAP.P001a.T3Statement := by
  apply SAP.P001a.Bridge.T3_correspondence.mpr
  refine ⟨⟨@AronowAudit.P001.Wave1.pda_at_mean_printed_contract_refuted,
    @AronowAudit.P001.Wave1.pda_extrapolation_witness_proof,
    @AronowAudit.P001.Wave1.pda_joint_cef_counterexample_proof⟩,
    contDiff_const, ?_⟩
  ext x
  by_cases hx : x ∈ Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc 1 2 <;>
    (simp only [Set.mem_union, Set.mem_Icc] at hx;
      simp [AronowAudit.P001.gapPDF, hx])

theorem SAP.P001a.T4 : SAP.P001a.T4WholeStatement := SAP.P001a.WH.W1.T4_whole

theorem SAP.P001a.T5 : SAP.P001a.T5WholeStatementW4 := SAP.P001a.WH.W4.T5W4_whole

theorem SAP.P001a.T6 : SAP.P001a.T6WholeStatement := SAP.P001a.WH.W1.T6_whole

theorem SAP.P001a.T7 : SAP.P001a.T7Statement.{u1,u2} := by
  apply SAP.P001a.Bridge.T7_correspondence.mpr
  exact ⟨@AronowAudit.P001.conditional_kl_mle_wrong_target, @AronowAudit.P001.Wave1.pooled_mle_covariate_marginal_bridge⟩

theorem SAP.P001a.T8 : SAP.P001a.T8WholeStatement := SAP.P001a.WH.W1.T8_whole

theorem SAP.P001a.T9 : SAP.P001a.T9Statement := by
  apply SAP.P001a.Bridge.T9_correspondence.mpr
  exact @AronowAudit.P001.Wave1.mixture_three_point_unbounded_proof

theorem SAP.P001a.T10 : SAP.P001a.T10Statement := by
  apply SAP.P001a.Bridge.T10_correspondence.mpr
  refine ⟨?_, @AronowAudit.P001.mixture_compact_attainment⟩
  intro n hn y hy
  have hu := AronowAudit.P001.Wave1.mixture_unbounded_positive_sample_proof hn y hy
  refine ⟨hu, ?_⟩
  rintro ⟨θ, hθ, hmax⟩
  obtain ⟨θ', hθ', hstrict⟩ := hu (AronowAudit.P001.mixtureLikelihood y θ)
  exact (not_lt_of_ge (hmax θ' hθ')) hstrict

theorem SAP.P001a.T11 : SAP.P001a.T11Statement := by
  apply SAP.P001a.Bridge.T11_correspondence.mpr
  exact ⟨@AronowAudit.P001.Wave1.unused_mixture_attained_mle_inconsistent, @AronowAudit.P001.finite_mixture_compact_attainment⟩

theorem SAP.P001a.T12 : SAP.P001a.T12WholeStatement := SAP.P001a.WH.W2.T12_whole

theorem SAP.P001a.T13 : SAP.P001a.T13Statement.{u1,u2} := by
  apply SAP.P001a.Bridge.T13_correspondence.mpr
  exact ⟨(by
      intro Ω instΩ μ instμ Z hiid hlaw hT2 hB2
      exact AronowAudit.P001.Wave1.TailA.hot_deck_bootstrap_counterexample_final μ Z hiid hlaw), (by
      intro Ω instΩ μ instμ Z hiid hlaw hT2 hB2
      exact AronowAudit.P001.Wave1.TailA.hot_deck_bootstrap_uniform_second_moment_final μ Z hiid hlaw), @AronowAudit.P001.hot_deck_bootstrap_constant_inequalities⟩

theorem SAP.P001a.T14 : SAP.P001a.T14Statement.{u1} := by
  apply SAP.P001a.Bridge.T14_correspondence.mpr
  exact ⟨(by
      intro Ω instΩ μ instμ Z hiid hlaw hT2 hB2
      exact AronowAudit.P001.Wave1.TailA.hot_deck_bootstrap_correction_final μ Z hiid hlaw), @AronowAudit.P001.Wave1.hot_deck_conditional_reuse_variance_proof⟩

theorem SAP.P001a.T15 : SAP.P001a.T15Statement.{u1,u2} := by
  apply SAP.P001a.Bridge.T15_correspondence.mpr
  exact ⟨(by
      intro Ω instΩ μ instμ Z hiid hlaw hT2 hB2
      exact AronowAudit.P001.Wave1.TailA.matching_bootstrap_counterexample_supporting_final μ Z hiid hlaw), @AronowAudit.P001.Wave1.matching_score_intercept_consistent_proof⟩

theorem SAP.P001a.T16 : SAP.P001a.T16Statement.{u1,u2} := by
  apply SAP.P001a.Bridge.T16_correspondence.mpr
  exact ⟨(by
      intro Ω instΩ μ instμ Z hiid hlaw hT2 hB2
      exact AronowAudit.P001.Wave1.TailA.estimated_matching_bootstrap_failure_final μ Z hiid hlaw), @AronowAudit.P001.Wave1.matching_score_intercept_consistent_proof, @AronowAudit.P001.estimated_score_matches_equal, @AronowAudit.P001.estimated_matching_statistic_equal, @AronowAudit.P001.Wave1.causal_matching_conditional_reuse_variance_proof⟩

theorem SAP.P001a.T17 : SAP.P001a.T17WholeStatement := SAP.P001a.WH.W2.T17_whole

theorem SAP.P001a.T18 : SAP.P001a.T18WholeStatement := SAP.P001a.WH.W1.T18_whole

theorem SAP.P001a.T19 : SAP.P001a.T19Statement := by
  apply SAP.P001a.Bridge.T19_correspondence.mpr
  exact @AronowAudit.P001.complete_overlap_without_uniform_positivity

