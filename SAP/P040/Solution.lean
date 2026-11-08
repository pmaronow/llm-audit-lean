import SAP.P040.Defs
import SAP.P040.Bridge
import SAP.P040.WH.W1.Proofs.T1
import AronowAudit.P040.P040_Binomial
import AronowAudit.P040.P040_Regression

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P040

noncomputable section

theorem T1 : SAP.P040.T1WholeStatement := SAP.P040.WH.W1.T1_whole

theorem T2 : T2Statement := by
  have he := Bridge.exact_interval_contains_eighty_percent
  have hb := Bridge.observed_upper_boundary_values
  refine ⟨Bridge.observed_proportion_rounds, Bridge.observed_tail_identities,
    Bridge.observedUpper_continuous, Bridge.observedUpper_strictMono,
    Bridge.observedLower_strictAnti, Bridge.observedUpper_hasDerivAt, ?_, hb.1, hb.2,
    Bridge.corrected_binomial_endpoints, ?_, he.1, he.2.1, ?_, ?_,
    he.2.2.1, he.2.2.2, ?_,
    ⟨Bridge.method_free_counterexample, Bridge.lower_bound_counterexample⟩⟩
  · intro p hp
    exact mul_pos (mul_pos (by norm_num) (pow_pos hp.1 _)) (sub_pos.mpr hp.2)
  · intro L U hL01 hU01 hL hU
    obtain ⟨a, b, c, d⟩ := Bridge.corrected_six_decimal_rounding hL01 hU01 hL hU
    exact ⟨⟨a, b⟩, ⟨c, d⟩⟩
  · rw [he.1]; norm_num
  · rw [he.2.1]; norm_num
  · intro p hp
    exact Bridge.exact_binomial_coverage hp

theorem T3 : T3Statement := by
  constructor
  · rw [roundsTwo, Bridge.printed_wald_arithmetic.1]
    norm_num
  · exact Bridge.printed_wald_arithmetic

theorem T4 : T4Statement := by
  have hi := Bridge.recorded_regression_identification
  have ha := Bridge.regression_witness_arithmetic
  have hr := Bridge.recorded_table_cells_round
  have hd := Bridge.corrected_regression_degrees_of_freedom
  have hqC : recordedSquaredStatistic true 2 = cafeSquaredStatistic := by
    simpa [tableSquaredStatistic] using
      Bridge.recorded_statistic_identity true 2
  have hqB : recordedSquaredStatistic true 1 = bulkSquaredStatistic := by
    simpa [tableSquaredStatistic] using Bridge.recorded_statistic_identity true 1
  have hn := Bridge.normal_reference_counterexample_bounds
  have ht := Bridge.corrected_student_reference_rounding
  refine ⟨Bridge.adjusted_columns_independent, hd.2.2.1, hd.2.2.2.1,
    Bridge.recorded_df_identity true, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1,
    ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, hqC, hqB,
    ha.2.2.2.2.1, ha.2.2.2.2.2.1, ha.2.2.2.2.2.2.1, ha.2.2.2.2.2.2.2,
    hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, Bridge.recorded_normal_counterexample, ?_, ?_⟩
  · norm_num [roundsSix, cafeCoefficientWitness]
  · unfold roundsSix
    constructor
    · apply Real.le_sqrt_of_sq_le
      norm_num [cafeVarianceWitness]
    · apply (Real.sqrt_lt (by norm_num [cafeVarianceWitness]) (by norm_num)).mpr
      norm_num [cafeVarianceWitness]
  · norm_num [roundsSix, cafeSquaredStatistic]
  · unfold roundsSix
    constructor
    · apply Real.le_sqrt_of_sq_le
      norm_num [cafeSquaredStatistic]
    · apply (Real.sqrt_lt (by norm_num [cafeSquaredStatistic]) (by norm_num)).mpr
      norm_num [cafeSquaredStatistic]
  · norm_num [roundsSix, bulkCoefficientWitness]
  · unfold roundsSix
    constructor
    · apply Real.le_sqrt_of_sq_le
      norm_num [bulkVarianceWitness]
    · apply (Real.sqrt_lt (by norm_num [bulkVarianceWitness]) (by norm_num)).mpr
      norm_num [bulkVarianceWitness]
  · norm_num [roundsSix, bulkSquaredStatistic]
  · unfold roundsSix
    constructor
    · apply Real.le_sqrt_of_sq_le
      norm_num [bulkSquaredStatistic]
    · apply (Real.sqrt_lt (by norm_num [bulkSquaredStatistic]) (by norm_num)).mpr
      norm_num [bulkSquaredStatistic]
  · simpa only [hqC] using hn.1
  · simpa only [hqC] using hn.2.1
  · simpa only [hqB] using hn.2.2.1
  · simpa only [hqB] using hn.2.2.2
  · simpa only [hqC] using ht.1
  · simpa only [hqB] using ht.2

theorem T5 : T5Statement := by
  have hd := Bridge.corrected_regression_degrees_of_freedom
  have hc : recordedSquaredStatistic true 2 = cafeSquaredStatistic := by
    simpa [tableSquaredStatistic] using Bridge.recorded_statistic_identity true 2
  have hb : recordedSquaredStatistic true 1 = bulkSquaredStatistic := by
    simpa [tableSquaredStatistic] using Bridge.recorded_statistic_identity true 1
  have hm : recordedSquaredStatistic false 1 = tableSquaredStatistic false 1 :=
    Bridge.recorded_statistic_identity false 1
  have ht := Bridge.corrected_student_reference_bounds
  have hr := Bridge.recorded_corrected_p_values
  have hl := Bridge.smallest_reference_p_bounds
  refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1,
    Bridge.unadjusted_columns_independent, Bridge.adjusted_columns_independent,
    Bridge.centered_weekdays_sum_zero, Bridge.adjusted_design_same_range,
    Bridge.recorded_df_identity, Bridge.student21_density_identity,
    ?_, ?_, ?_, ?_, hr.1, hr.2, ?_, ?_, ?_, ?_, ?_, ?_,
    Bridge.recorded_normal_counterexample⟩
  · simpa only [hc] using ht.1
  · simpa only [hc] using ht.2.1
  · simpa only [hb] using ht.2.2.1
  · simpa only [hb] using ht.2.2.2
  · intro a o
    have hq := Bridge.recorded_statistic_identity a o
    have hn := Bridge.recorded_effects_not_significant a o
    have hmin := Bridge.unadjusted_bulk_minimizes_reference_p a o
    have hbd := Bridge.table_statistics_bounded.2 a o
    refine ⟨hq, ?_, ?_, hn.1, hn.2, ?_, ?_⟩
    · simpa only [hq] using hbd.1
    · simpa only [hq, hm] using hbd.2
    · simpa only [hq, hm, Bridge.recorded_df_identity] using hmin.1
    · simpa only [hq, hm] using hmin.2
  · simpa only [hm] using Bridge.table_statistics_bounded.1
  · simpa only [hm] using hl.1
  · simpa only [hm] using hl.2.1
  · simpa only [hm] using hl.2.2.1
  · simpa only [hm] using hl.2.2.2

end
end SAP.P040
