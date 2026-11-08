import SAP.P013b.Defs
import SAP.P013b.Bridge
import AronowAudit.P013.P013_Audit
import AronowAudit.P013.P013_Later
import AronowAudit.P013.Wave1.PrintedWald

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P013b
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset

theorem SAP.P013b.T15 : SAP.P013b.T15Statement := by
  intro Ω _ N K P F _ d e hne hd he
  exact ⟨fun hj => Bridge.covarianceHT_conservative F d e hne hd he hj,
    fun hj hy => Bridge.covarianceHT_unbiased_no_effect F d e hne hd he hj hy,
    Bridge.covarianceA_conservative F d e hne hd he,
    Bridge.effectVariance_conservative F d e hne hd he⟩

theorem SAP.P013b.T16 : SAP.P013b.T16Statement := by
  intro Ω _ N K P F hN d hd g
  exact ⟨Bridge.differenceTotal_unbiased F d g hd,
    Bridge.differenceTotal_residual F d g, Bridge.htCount_unbiased F d hd,
    Bridge.hajek_bias_bound F hN d hd⟩

theorem SAP.P013b.T17 : SAP.P013b.T17Statement := by
  intro Ω _ N K P F _ yr d e hne hm hd he
  exact ⟨Bridge.misspecified_expectation F yr d hm hd,
    Bridge.misspecified_contrast F yr d e hne hm hd he⟩

theorem SAP.P013b.T18 : SAP.P013b.T18Statement := by
  intro hall
  apply AronowAudit.P013.Wave1.printed_wald_coverage_refuted
  intro S hn hp hc3 hc5 hc6 α ha hb
  exact hall (Bridge.fromSequence S) hn hp hc3 hc5 hc6 α ha hb

theorem SAP.P013b.T19 : SAP.P013b.T19Statement := by
  exact Bridge.htEffect_consistency

theorem SAP.P013b.T20 : SAP.P013b.T20Statement := by
  exact Bridge.simulation_matrices_iid

theorem SAP.P013b.T21 : SAP.P013b.T21Statement := by
  refine ⟨Bridge.location_counterexample_hypotheses,
    Bridge.location_counterexample_targets, Bridge.location_counterexample_enumeration,
    Bridge.location_translation_counterexample, Bridge.location_counterexample_moments,
    Bridge.location_counterexample_joint_repair, ?_, ?_⟩
  · intro z i
    simp [observed, locationPopulation, shiftPopulation]
  · intro z
    obtain ⟨wk, wl, sk, sl, sc⟩ := Bridge.location_counterexample_enumeration z
    have hb := Bridge.location_counterexample_targets
    rw [wk, wl, sk, sl, sc, hb.2.2.2.1 z 1, hb.2.2.2.1 z 0, hb.2.2.2.2 z]
    by_cases h : z = 2 <;> norm_num [h]

theorem SAP.P013b.T22 : SAP.P013b.T22Statement := by
  refine ⟨@Bridge.differenceTotal_shift_change, @Bridge.differenceTotal_shift_error,
    @Bridge.differenceTotal_equivariance_iff, @Bridge.differenceTotal_joint_translation,
    @Bridge.difference_joint_translation_properties, @Bridge.differenceEffect_shift_error,
    @Bridge.difference_fixed_prediction_translation, @Bridge.exposureWeight_unbiased,
    @Bridge.ht_fixed_translation, @Bridge.translation_error_mean_zero,
    @Bridge.fixed_translation_mean_zero, @Bridge.fixed_count_calibration, ?_⟩
  constructor
  · intro d i
    fin_cases d <;> fin_cases i <;>
      norm_num [pi, expectation, indicator, calibrationPopulation, calibrationDesign,
        Fin.sum_univ_two]
  · have hc : ∀ z, ∑ i, indicator calibrationPopulation.exposure i 1 z = (1 : ℝ) := by
      intro z
      fin_cases z <;> norm_num [indicator, calibrationPopulation, Fin.sum_univ_two]
    have hm : ∀ i, pi calibrationPopulation i 1 = (1 : ℝ) / 2 := by
      intro i
      fin_cases i <;>
        norm_num [pi, expectation, indicator, calibrationPopulation, calibrationDesign,
          Fin.sum_univ_two]
    simpa using Bridge.fixed_count_calibration calibrationPopulation (by decide) 1 1
      (by decide) (by simpa using hc) (by simpa using hm) (fun _ => 0) 1

theorem SAP.P013b.T23 : SAP.P013b.T23Statement := by
  refine ⟨Bridge.two_report_hypotheses, Bridge.two_report_data_same,
    Bridge.two_report_estimator, Bridge.two_report_moments, Bridge.two_wearing_effects_and_losses,
    Bridge.two_report_biases, Bridge.two_report_nonidentification,
    Bridge.two_respondent_comparison, ?_, ?_, ?_⟩
  · intro world z i
    rw [Bridge.two_report_data_same world]
    rcases z with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> fin_cases i <;>
      norm_num [recordedData, twoWearPopulation, twoRecording, recordedPopulation, observed]
  · intro world
    have h := Bridge.two_wearing_effects_and_losses world
    rw [Bridge.two_report_biases world, h.2.1, h.2.2]
    fin_cases world <;> norm_num
  · intro world
    rw [(Bridge.two_respondent_comparison world).2.1, (Bridge.two_report_moments world).1]
    norm_num

theorem SAP.P013b.T24 : SAP.P013b.T24Statement := by
  refine ⟨@Bridge.corrected_recorded_outcome, @Bridge.no_lost_wearing_suffices,
    @Bridge.dropping_zero_outcomes, @Bridge.public_reconstruction_HT_scaling,
    Bridge.hajek_exclusion_no_common_factor, ?_⟩
  have h := Bridge.public_reconstruction_factors
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem SAP.P013b.T25 : SAP.P013b.T25Statement := by
  refine ⟨Bridge.school_support_counterexample, Bridge.school_example_potential_hypotheses,
    @Bridge.school_two_HT_reduction, ?_, ?_, @Bridge.school_correct_joint_unbiased,
    Bridge.school_wrong_joint_counterexample, Bridge.school_wrong_joint_biases, ?_, ?_, ?_⟩
  · intro α hosts a b hab q z _
    exact Bridge.school_two_variance_reduction hosts a b hab q z
  · intro α S hosts a b hab p q ha hb hp _
    exact Bridge.school_two_moments S hosts a b hab p q ha hb hp
  · intro a
    have hb : uniformSchoolProbability schoolBSupport (fun z => schoolBHosts z a = true) = 1/2 := by
      simpa [schoolBHosts] using Bridge.school_B_marginal a
    have hc : uniformSchoolProbability schoolCSupport (fun z => schoolCHosts z a = true) = 1/2 := by
      simpa [schoolCHosts] using Bridge.school_C_marginal a
    refine ⟨hb, ?_, hc, ?_⟩
    · rw [Bridge.uniform_school_probability_mean]
      simpa using Bridge.school_local_mean schoolBSupport Bridge.school_supports_nonempty.1
        schoolBHosts a (fun b => if b = false then 1 else 0) hb
    · rw [Bridge.uniform_school_probability_mean]
      simpa using Bridge.school_local_mean schoolCSupport Bridge.school_supports_nonempty.2
        schoolCHosts a (fun b => if b = false then 1 else 0) hc
  · refine ⟨?_, ?_, ?_⟩
    · simpa [schoolBHosts] using Bridge.school_B_joint (0,0) (0,1) (by decide)
    · simpa [schoolBHosts] using Bridge.school_B_joint (0,0) (1,0) (by decide)
    · simpa [schoolCHosts] using Bridge.school_C_joint (0,0) (0,1) (by decide)
  · have h : Nat.choose 56 28 = 7648690600760440 :=
      Bridge.school_assignment_counts.2.2.1.symm.trans Bridge.school_assignment_counts.2.2.2
    norm_num [h]

theorem SAP.P013b.T26 : SAP.P013b.T26Statement := by
  refine ⟨Bridge.school_assignment_counts, Bridge.school_B_embeds_C,
    Bridge.school_B_marginal, Bridge.school_C_marginal, Bridge.school_B_joint,
    Bridge.school_C_joint, Bridge.school_joint_differences, Bridge.school_B_pair_distribution,
    Bridge.school_C_pair_distribution, @Bridge.school_exposure_probabilities_unchanged,
    Bridge.school_hosted_no_exposure, @Bridge.school_no_exposure_probabilities, ?_, ?_, ?_⟩
  · exact ⟨Bridge.school_support_counterexample.2.1, Bridge.school_support_counterexample.2.2.1⟩
  · norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]
  · intro a b hab
    rw [Bridge.school_C_joint a b hab, Bridge.school_B_joint a b hab]
    by_cases h : a.1 = b.1 <;> norm_num [h]

theorem SAP.P013b.T27 : SAP.P013b.T27Statement := by
  exact @Bridge.section10_wearing_unbiased
