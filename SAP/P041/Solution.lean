import SAP.P041.Defs
import SAP.P041.Bridge
import SAP.P041.WH.W1.Proofs.T12
import SAP.P041.WH.W1.Proofs.T7
import SAP.P041.WH.W1.Proofs.T8
import SAP.P041.WH.W1.Proofs.T9
import SAP.P041.WH.W2.Proofs.T10

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open SAP.P041 SAP.P041.Bridge Matrix
open scoped BigOperators

theorem SAP.P041.T1 : T1Statement := by
  refine ⟨?_, ?_, common_bias_countermodel⟩
  · intro q hq0 hq1
    obtain ⟨hp, hn, hr, hi, hne⟩ := proportional_hazards q hq0 hq1
    exact ⟨hp, hn, hr, hi, hne, twelve_hour_survival q hq0⟩
  · intro q t hq0 _ _
    exact exponential_survival_power_laws q t hq0

theorem SAP.P041.T2 : T2Statement := by
  exact ⟨corrected_former_nondetection, corrected_former_imprecision,
    former_wald_endpoint_enclosures, corrected_between_relative_effects,
    corrected_normal_p_approximations_proof, observed_early_contrasts,
    smaller_contrast_does_not_exclude_common_bias⟩

theorem SAP.P041.T3 : T3Statement := by
  exact ⟨risk_percentages_counterexample, symmetric_understates_relative, risk_measure_gaps⟩

theorem SAP.P041.T4 : T4Statement := by
  exact corrected_risk_percentages

theorem SAP.P041.T5 : T5Statement := by
  refine ⟨@scrutiny_no_direct_effect, (fun m _ z => slow_schedule_zero m z), ?_, ?_,
    random_order_block_counterexample, balanced_scrutiny_general_proof, ?_,
    study_one_size_scrutiny_proof, ?_, fixed_calendar_block_unbiased, independent_citation_boundary⟩
  · intro m _
    simp only [balancedExpectation, slow_schedule_zero, Finset.sum_const_zero, zero_div]
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := block_two_outcomes
    refine ⟨block_two_sequences, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [scrutinyBlockCase, citationContrast, h1, h2, h3, h4, h5, h6]
      norm_num [Finset.sum_insert, Finset.sum_singleton, Finset.sum_sdiff,
        Finset.subset_univ, Fin.sum_univ_succ]
  · intro m hm z hz
    rw [((balanced_scrutiny_general_proof m hm).2.2.1 z hz).2]
  · intro m hm Y
    simpa using random_order_without_interference m hm (fun r _ => Y r)

theorem SAP.P041.T6 : T6Statement := by
  refine ⟨random_order_without_interference, ?_, block_without_interference,
    adaptive_protocol_estimands_general_proof, adaptive_protocol_estimands_differ, ?_⟩
  · intro m hm c
    simpa using random_order_without_interference m hm (fun r _ => c r)
  · constructor
    · simpa using random_order_without_interference 2 (by norm_num)
        (fun r _ => (![0,0,1,1] : Fin 4 → ℝ) r)
    · have h := (adaptive_protocol_estimands_general_proof 50 (by norm_num)).2.2.1
      norm_num at h ⊢
      exact h

theorem SAP.P041.T7 : SAP.P041.T7WholeStatement := SAP.P041.WH.W1.T7_whole

theorem SAP.P041.T8 : SAP.P041.T8WholeStatement := SAP.P041.WH.W1.T8_whole

theorem SAP.P041.T9 : SAP.P041.T9WholeStatement := SAP.P041.WH.W1.T9_whole

theorem SAP.P041.T10 : SAP.P041.T10WholeStatement := SAP.P041.WH.W2.T10_whole

theorem SAP.P041.T11 : T11Statement := by
  exact ⟨printed_former_normal_p_enclosures_proof, former_subgroup_nondetections⟩

theorem SAP.P041.T12 : SAP.P041.T12WholeStatement := SAP.P041.WH.W1.T12_whole
