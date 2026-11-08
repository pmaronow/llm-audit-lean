import SAP.P013a.WH.W1.Proofs.T1
import SAP.P013a.WH.W1.Proofs.T2
import SAP.P013a.WH.W1.Proofs.T8
import SAP.P013a.WH.W1.Proofs.T9
import SAP.P013a.WH.W1.Proofs.T14
import SAP.P013a.Defs
import SAP.P013a.Bridge
import AronowAudit.P013.P013_Audit
import AronowAudit.P013.P013_Reporting
import AronowAudit.P013.P013_ConfidenceCompletion
import AronowAudit.P013.Wave1.Gap.GLP013P012B1
import AronowAudit.P013.Wave1.Gap.GLP013P012B2
import AronowAudit.P013.Wave1.Gap.GLP013P012B3
import AronowAudit.P013.Wave1.Gap.GP013P012B1
import AronowAudit.P013.Wave1.Gap.FidP013

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013a

open scoped BigOperators Topology
open Filter Finset Bridge
noncomputable section

theorem T1 : SAP.P013a.T1WholeStatement := SAP.P013a.WH.W1.T1_whole

theorem T2 : SAP.P013a.T2WholeStatement := SAP.P013a.WH.W1.T2_whole

theorem T3 : T3Statement := by
  exact ⟨AronowAudit.P013.signed_replication_counterexample,
    AronowAudit.P013.signed_log_rule_counterexample,
    AronowAudit.P013.zero_total_replication_counterexample⟩

theorem T4 : T4Statement := by
  constructor
  · intro Ω _ N K P F hN d hd R hR p0 hm
    have he : expectation (independentProduct P (replicateDesign P R)) (simulatedHTTotal F d R) =
        potentialTotal F d-∑ i, F.outcome i d*(1-pi F i d)^(R+1) :=
      AronowAudit.P013.simulated_expectation (toPopulation F) hN d hd R hR
    have hb := AronowAudit.P013.simulated_bias_repaired (toPopulation F) hN d hd R hR p0 hm
    refine ⟨?_, he, hb.1, ?_⟩
    · simpa only [mul_sub, mul_one, sum_sub_distrib, potentialTotal] using he
    · intro ht
      have h := hb.2 ht
      refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
      intro hs
      have hc := h.2.2.1 hs
      refine ⟨hc.1, hc.2, ?_⟩
      intro b hbp hr
      apply h.2.2.2 b hbp
      simpa only [hc.1, div_one] using hr
  · exact AronowAudit.P013.replicate_rule_numerical

theorem T5 : T5Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N A B hd
    exact AronowAudit.P013.printed_identity_vacuous A B hd
  · intro Ω _ N K P D
    have h := AronowAudit.P013.printed_identity_dependency (toDesign P) D
    refine ⟨h.1, h.2, ?_⟩
    intro i
    simp
  · intro q
    let h := fun i j : Fin (3*q) => decide (i ≠ j ∧ i.val/3=j.val/3)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      simp only [ne_eq, eq_comm]
    · intro i
      simp [h]
    · intro A B hd
      exact (AronowAudit.P013.printed_triangles_vacuous q A B hd).1
    · exact (AronowAudit.P013.printed_triangles_vacuous q ∅ ∅ (disjoint_empty_left _)).2
    · intro Ω _ K P D A B hd hn
      rcases (AronowAudit.P013.printed_triangles_vacuous q A B hd).1.mp hn with ⟨rfl, rfl⟩
      exact (AronowAudit.P013.printed_identity_dependency (toDesign P) D).1 ∅ ∅ hd
        ((AronowAudit.P013.printed_identity_vacuous ∅ ∅ hd).mpr ⟨rfl, rfl⟩)
  · intro N
    have h := AronowAudit.P013.shared_exposure_counterexample N
    refine ⟨h.1, h.2.1, ?_, h.2.2⟩
    intro i
    simp
  · exact AronowAudit.P013.shared_pair_count
  · exact ⟨fromSequence AronowAudit.P013.sharedSequence,
      AronowAudit.P013.shared_sequence_counterexample⟩

theorem T6 : T6Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro N h A B
    exact ⟨AronowAudit.P013.corrected_edge_equivalence h A B,
      fun hs => AronowAudit.P013.corrected_symmetric_equivalence h hs A B⟩
  · intro Ω _ N K P F h hg
    refine ⟨?_, ?_⟩
    · intro i j hz
      have hn : ¬ (i=j ∨ h i j=true ∨ h j i=true) := by
        intro he
        simpa [graphPairIndicator, he] using hz
      have hh : i ≠ j ∧ h i j=false ∧ h j i=false := by simpa using hn
      exact AronowAudit.P013.genuine_implies_pair_independent
        (toPopulation F) h hg i j hh.1 hh.2.1 hh.2.2
    · intro m hb
      exact ⟨AronowAudit.P013.graph_pair_count h m hb,
        fun hs => AronowAudit.P013.graph_pair_count_symmetric h m hs hb⟩
  · intro S h5
    exact AronowAudit.P013.Wave1.directed_condition5_implies_condition4 (toSequence S) h5

theorem T7 : T7Statement := by
  exact ⟨AronowAudit.P013.Wave1.block_finite_identities_proof,
    AronowAudit.P013.Wave1.block_asymptotic_positive_estimator,
    AronowAudit.P013.Wave1.block_endpoint_bounds_proof,
    AronowAudit.P013.Wave1.block_asymptotic_counterexample_proof⟩

theorem T8 : SAP.P013a.T8WholeStatement := SAP.P013a.WH.W1.T8_whole

theorem T9 : SAP.P013a.T9WholeStatement := SAP.P013a.WH.W1.T9_whole

theorem T10 : T10Statement := by
  refine ⟨AronowAudit.P013.wald_center, ?_, ?_, AronowAudit.P013.table2_two_rows⟩
  · rintro e L U ⟨he, hL, hU, hm⟩
    exact AronowAudit.P013.wls_d101_impossible e L U he hL hU hm
  · rintro e L U ⟨he, hL, hU, hm⟩
    exact AronowAudit.P013.wls_d111_impossible e L U he hL hU hm

theorem T11 : T11Statement := by
  intro U neighbors i n hi hsub hex hdeg hn hmax
  have hc := AronowAudit.P013.complete_randomization_degree39_counts U neighbors i n
    hi hsub hex hdeg hn hmax
  have h40 : 40 ≤ U.card := by omega
  have hf : completeProbability U n (noExposure i neighbors) =
      ((U.card : ℝ)-39-n)/n*completeProbability U n (isolatedExposure i neighbors) := by
    rw [show completeProbability U n (noExposure i neighbors) = _ from hc.2,
      show completeProbability U n (isolatedExposure i neighbors) = _ from hc.1]
    exact AronowAudit.P013.degree39_choose_ratio U.card n h40 hn hmax
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 ≤ completeProbability U n (isolatedExposure i neighbors) := by
    unfold completeProbability
    positivity
  refine ⟨hc.1, hc.2, hf, ?_⟩
  intro hr
  have hr' : (U.card : ℝ) ≤ 10*n+5 := by exact_mod_cast hr
  exact ⟨AronowAudit.P013.degree39_ratio_bound _ _ _ _ hnp hr' hp hf,
    fun h => AronowAudit.P013.degree39_small_p _ _ _ _ hnp hr' hp hf h,
    fun h => AronowAudit.P013.degree39_large_q _ _ _ _ hnp hr' hp hf h⟩

theorem T12 : T12Statement := by
  constructor
  · intro h
    apply AronowAudit.P013.ConfidenceFollowup02.simulated_bias_as_printed_refuted.{0}
    intro Ω _ N K P F hN d hd R p0 hm ht
    exact h (fromPopulation F) hN d hd R p0 hm ht
  · intro h
    apply AronowAudit.P013.ConfidenceFollowup02.simulated_rule_as_printed_refuted.{0}
    intro Ω _ N K P F hN d hd R p0 hm ht b hb hr
    exact h (fromPopulation F) hN d hd R p0 hm ht b hb hr

theorem T13 : T13Statement := by
  constructor
  · intro Ω _ N K P F _ d hd
    exact ⟨AronowAudit.P013.ht_unbiased (toPopulation F) d hd,
      AronowAudit.P013.ht_variance_formula (toPopulation F) d⟩
  · intro Ω _ N K P F _ d e hne hd he
    exact ⟨AronowAudit.P013.htEffect_unbiased (toPopulation F) d e hd he,
      AronowAudit.P013.htEffect_variance (toPopulation F) d e,
      AronowAudit.P013.ht_covariance_formula (toPopulation F) d e hne hd he⟩

theorem T14 : SAP.P013a.T14WholeStatement := SAP.P013a.WH.W1.T14_whole

end
end SAP.P013a
