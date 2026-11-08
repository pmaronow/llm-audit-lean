import SAP.P044.Defs
import SAP.P044.Bridge
import AronowAudit.P044.Wave1.Gap.GP044B1
import AronowAudit.P044.Wave1.Gap.GP044B2
import AronowAudit.P044.Wave1.Gap.GP044B3
import AronowAudit.P044.Wave1.Gap.GP044B4
import AronowAudit.P044.Wave1.Checks.Fid2P044Contracts
import AronowAudit.P044.P044_IndependentBank
import SAP.P044.WH.W1.Proofs.T2
import SAP.P044.WH.W1.Proofs.T3
import SAP.P044.WH.W1.Proofs.T7
import SAP.P044.WH.W1.Proofs.T9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044

open Finset MeasureTheory ProbabilityTheory Bridge
open scoped BigOperators unitInterval

noncomputable section

set_option maxRecDepth 2000
set_option maxHeartbeats 1200000

/-- Only definitional transport and the common label equivalence are applied here. -/
macro "transport " t:term : tactic =>
  `(tactic| (have transported := $t
             try simp [Bool.forall_bool] at transported ⊢
             all_goals (convert @transported using 0 <;> rfl)))

theorem T1 : T1Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · transport AronowAudit.P044.Wave1.clique_variance_counterexample_proof
  · constructor
    · intro i
      have h := AronowAudit.P044.Wave1.clique_full_counts_proof.1
      transport And.intro (h i .d01) (h i .d00)
    · intro i j hij
      have h := AronowAudit.P044.Wave1.clique_full_counts_proof.2 i j
      have h' := And.intro (h .d01 .d01 (Or.inl rfl) (Or.inl rfl))
        (And.intro (h .d00 .d00 (Or.inr rfl) (Or.inr rfl))
          (h .d01 .d00 (Or.inl rfl) (Or.inr rfl)))
      simp only [AronowAudit.P044.cliqueFullJoint, if_neg hij] at h'
      transport h'
  · transport AronowAudit.P044.Wave1.clique_structure_proof
  · transport AronowAudit.P044.Wave1.clique_all_fixed_table_counterexamples_proof
  · transport AronowAudit.P044.Wave1.clique_exact_profile_estimates_proof
  · constructor
    · intro t i
      have h := AronowAudit.P044.Wave1.clique_retained_weights_proof.1
      transport And.intro (h t i .d01) (h t i .d00)
    · transport AronowAudit.P044.Wave1.clique_retained_weights_proof.2
  · intro t
    refine ⟨AronowAudit.P044.cliqueRelabeling t, ?_⟩
    have h := AronowAudit.P044.Wave1.clique_relabeling_verified_proof t
    transport And.intro h.1 h.2.1

theorem T2 : SAP.P044.T2WholeStatement := SAP.P044.WH.W1.T2_whole

theorem T3 : SAP.P044.T3WholeStatement := SAP.P044.WH.W1.T3_whole

theorem T4 : T4Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω D N _ _ hN P f y a b hab ha hb
    have h := AronowAudit.P044.ht_unbiased hN (toDesign P) f y a b hab ha hb
    have h' := AronowAudit.P044.ht_unbiased hN (toDesign P) f y b a (Ne.symm hab) hb ha
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, h'.1⟩
  · intro Ω D N _ _ hN P z f y a b hab j hz δ hδ T
    exact AronowAudit.P044.support_necessary hN (toDesign P) z f y a b hab j hz δ hδ T
  · intro Ω D N _ _ P f y a b hab hS
    exact AronowAudit.P044.common_support_unbiased (toDesign P) f y a b hab hS
  · transport AronowAudit.P044.star_common_support
  · intro N M hN hM hMN A hsym hdiag i
    transport AronowAudit.P044.complete_randomization_support N M hN hM hMN A hsym hdiag i
  · intro A hsym hdiag i
    have h := (AronowAudit.P044.complete_randomization_support 1000 100
      (by norm_num) (by norm_num) (by norm_num) A hsym hdiag i).2.2.2.2
    have h' := h.trans (AronowAudit.P044.complete_support_1000_100 _)
    transport h' 
  · refine ⟨?_, ?_, ?_⟩
    · transport AronowAudit.P044.star_counterexample.2.2.1 0 .d00
    · transport AronowAudit.P044.star_counterexample.2.2.1 0 .d10
    · exact ⟨AronowAudit.P044.star_counterexample.1, by
        norm_num [degree, starAdj, Fin.sum_univ_succ]⟩

theorem T5 : T5Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact AronowAudit.P044.triangle_baseline_witness
  · exact AronowAudit.P044.triangle_two_walk_matrix
  · transport AronowAudit.P044.triangle_outcome_vectors
  · exact AronowAudit.P044.negative_baseline_rectangle
  · exact AronowAudit.P044.baseline_not_halfNormal
  · exact AronowAudit.P044.triangle_rectangle_cdf
  · exact AronowAudit.P044.triangle_cdf_rectangle_negative
  · exact AronowAudit.P044.halfNormal_mean
  · exact AronowAudit.P044.halfNormal_variance
  · exact AronowAudit.P044.halfNormal_second_moment
  · exact AronowAudit.P044.corrected_baseline_moments
  · exact AronowAudit.P044.triangle_moment_comparison
  · exact AronowAudit.P044.nonisolated_baseline_mean_shift
  · exact AronowAudit.P044.baseline_memLp
  · exact (memLp_id_gaussianReal (μ := 0) (v := 1) 2).abs
  · intro a ha
    have hm : (∫ x, baseline a x.1 x.2 ∂normalPair) = a * Real.sqrt (2 / Real.pi) + 1 :=
      (AronowAudit.P044.corrected_baseline_moments a (by linarith)).1
    rw [hm, AronowAudit.P044.halfNormal_mean]
    ring

theorem T6 : T6Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N B i; simp [dilatedOutcomes]
  · exact AronowAudit.P044.corrected_baseline_moments
  · exact AronowAudit.P044.halfNormal_mean
  · exact AronowAudit.P044.halfNormal_second_moment
  · exact AronowAudit.P044.baseline_memLp
  · intro N hN B; transport AronowAudit.P044.dilated_effects B
  · transport AronowAudit.P044.triangle_realized_effects
  · norm_num [Fin.sum_univ_succ]
  · transport @AronowAudit.P044.generated_effect_mean
  · transport @AronowAudit.P044.generated_effect_scale
  · transport @AronowAudit.P044.halfNormal_population_effect
  · intro N hN A; exact generatedEffect_integrable A
  · intro Ω _ N hN P _ B hLaw
    exact effect_integrable P B (fun i => (hLaw i).integrable halfNormal_integrable)

theorem T7 : SAP.P044.T7WholeStatement := SAP.P044.WH.W1.T7_whole

theorem T8 : T8Statement := by
  constructor
  · intro R N D _ _ hR hN f y w a hw
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j b
      exact AronowAudit.P044.exhaustive_probabilities hR f i j a b
    · exact AronowAudit.P044.htMean_expectation _ f y w a
    · intro hp
      rw [show expect (fun _ : Fin R => (1/R : ℝ))
          (htMean f y (marginal (fun _ : Fin R => (1/R : ℝ)) f) a) = _ from
        AronowAudit.P044.htMean_expectation _ f y _ a]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact mul_div_cancel_right₀ _ (ne_of_gt (hp i))
    · exact AronowAudit.P044.exhaustive_smoothing_bias hR f y a
    · intro i
      exact AronowAudit.P044.smoothing_bias_multiplier R (exposureCount f i a) hR
    · intro hK i
      exact AronowAudit.P044.smoothed_not_distribution R (exposureCount f i)
        (exposure_count_partition f i) hK
  · intro Ω _ μ _ R p D C hD hC hDC hp hp1
    exact AronowAudit.P044.IndependentBank.independent_bank_expectation μ R p D C hD hC hDC hp hp1

theorem T9 : SAP.P044.T9WholeStatement := SAP.P044.WH.W1.T9_whole

theorem T10 : T10Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact @AronowAudit.P044.crossCommunity_probability_zero
  · intro Ω C N _ _ P G _ c hz
    exact AronowAudit.P044.no_cross_edges_on_support (toDesign P) G c hz
  · intro N C hN G _ c hd hw
    exact ⟨G.sum_degrees_eq_twice_card_edges,
      AronowAudit.P044.within_community_share hN G c hd hw⟩
  · intro Ω C N _ hN P G _ c hd hw
    have h := AronowAudit.P044.returned_graph_expectations hN (toDesign P) G c hd hw
    refine ⟨h.1, h.2, ?_, ?_⟩
    · have hg := congrArg (fun x : ℝ => x - 7/10) h.1
      norm_num at hg
      transport hg
    · have hg := congrArg (fun x : ℝ => x - 7/10) h.2
      norm_num at hg
      transport hg

theorem T13 : T13Statement := by
  intro N A hdiag hN
  have h := AronowAudit.P044.Wave1.baseline_description_refuted_at_every_graph_of_pos N A hdiag hN
  dsimp only [AronowAudit.P044.Wave1.Fid2P044Contracts.printedContractAt] at h
  transport h

end
end SAP.P044
