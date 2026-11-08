import SAP.P040.Defs
import AronowAudit.P040.P040_Regression

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P040.Bridge
open scoped BigOperators

/- Each type below is the exported project type expressed with shared SAP definitions.
The proof is only transport along definitional equality. -/

theorem regression_witness_arithmetic :
    0 < cafeVarianceWitness ∧ 0 < bulkVarianceWitness ∧
    cafeCoefficientWitness ^ 2 / cafeVarianceWitness = cafeSquaredStatistic ∧
    bulkCoefficientWitness ^ 2 / bulkVarianceWitness = bulkSquaredStatistic ∧
    0 < cafeSquaredStatistic ∧ cafeSquaredStatistic < (8 : ℝ) / 5 ∧
    0 < bulkSquaredStatistic ∧ bulkSquaredStatistic < (8 : ℝ) / 5 := by
  exact AronowAudit.P040.regression_witness_arithmetic

theorem normal_reference_counterexample_bounds :
    (58198 / 100000 : ℝ) < normalReferenceP cafeSquaredStatistic ∧
    normalReferenceP cafeSquaredStatistic < (58199 / 100000 : ℝ) ∧
    (27530 / 100000 : ℝ) < normalReferenceP bulkSquaredStatistic ∧
    normalReferenceP bulkSquaredStatistic < (27531 / 100000 : ℝ) := by
  exact AronowAudit.P040.normal_reference_counterexample_bounds

theorem normal_reference_rounding_mismatch :
    roundsTwo (normalReferenceP cafeSquaredStatistic) (58 / 100) ∧
    ¬roundsTwo (normalReferenceP cafeSquaredStatistic) (59 / 100) ∧
    roundsTwo (normalReferenceP bulkSquaredStatistic) (28 / 100) ∧
    ¬roundsTwo (normalReferenceP bulkSquaredStatistic) (29 / 100) := by
  exact AronowAudit.P040.normal_reference_rounding_mismatch

theorem student21_density_identity (t : ℝ) :
    studentReferenceDensity 21 t = student21Density t := by
  exact AronowAudit.P040.student21_density_identity t

theorem corrected_student_reference_bounds :
    (58779 / 100000 : ℝ) < studentReferenceP cafeSquaredStatistic 21 ∧
    studentReferenceP cafeSquaredStatistic 21 < (58780 / 100000 : ℝ) ∧
    (28766 / 100000 : ℝ) < studentReferenceP bulkSquaredStatistic 21 ∧
    studentReferenceP bulkSquaredStatistic 21 < (28767 / 100000 : ℝ) := by
  exact AronowAudit.P040.corrected_student_reference_bounds

theorem corrected_student_reference_rounding :
    roundsTwo (studentReferenceP cafeSquaredStatistic 21) (59 / 100) ∧
    roundsTwo (studentReferenceP bulkSquaredStatistic 21) (29 / 100) := by
  exact AronowAudit.P040.corrected_student_reference_rounding

theorem unadjusted_columns_independent : Function.Injective unadjustedDesign.mulVecLin := by
  exact AronowAudit.P040.unadjusted_columns_independent

theorem adjusted_columns_independent : Function.Injective adjustedDesign.mulVecLin := by
  exact AronowAudit.P040.adjusted_columns_independent

theorem centered_weekdays_sum_zero (i : Fin 30) :
    (∑ c : Fin 7, centeredWeekday c i) = 0 := by
  exact AronowAudit.P040.centered_weekdays_sum_zero i

theorem adjusted_design_same_range :
    LinearMap.range originalAdjustedDesign.mulVecLin = LinearMap.range adjustedDesign.mulVecLin := by
  exact AronowAudit.P040.adjusted_design_same_range

theorem corrected_regression_degrees_of_freedom :
    Fintype.card (Fin 30) = 30 ∧ unadjustedDesign.rank = 2 ∧ adjustedDesign.rank = 9 ∧
    originalAdjustedDesign.rank = 9 ∧
    30 - unadjustedDesign.rank = 28 ∧ 30 - originalAdjustedDesign.rank = 21 := by
  exact AronowAudit.P040.corrected_regression_degrees_of_freedom

theorem table_statistics_bounded :
    tableSquaredStatistic false 1 < (8 : ℝ) / 5 ∧
    ∀ a : Bool, ∀ o : Fin 4, 0 < tableSquaredStatistic a o ∧
      tableSquaredStatistic a o ≤ tableSquaredStatistic false 1 := by
  exact AronowAudit.P040.table_statistics_bounded

theorem recorded_regression_identification :
    olsCoefficients adjustedDesign salesCafe 1 = cafeCoefficientWitness ∧
    hc1Variance adjustedDesign salesCafe 1 = cafeVarianceWitness ∧
    olsCoefficients adjustedDesign salesBulk 1 = bulkCoefficientWitness ∧
    hc1Variance adjustedDesign salesBulk 1 = bulkVarianceWitness ∧
    (∀ o : Fin 4, olsSquaredStatistic unadjustedDesign (tableOutcome o) 1 = tableSquaredStatistic false o) ∧
    (∀ o : Fin 4, olsSquaredStatistic adjustedDesign (tableOutcome o) 1 = tableSquaredStatistic true o) := by
  exact AronowAudit.P040.recorded_regression_identification

theorem smallest_reference_p_bounds :
    (22533 / 100000 : ℝ) < studentReferenceP (tableSquaredStatistic false 1) 28 ∧
    studentReferenceP (tableSquaredStatistic false 1) 28 < (22534 / 100000 : ℝ) ∧
    (21504 / 100000 : ℝ) < normalReferenceP (tableSquaredStatistic false 1) ∧
    normalReferenceP (tableSquaredStatistic false 1) < (21505 / 100000 : ℝ) := by
  exact AronowAudit.P040.smallest_reference_p_bounds

theorem unadjusted_bulk_minimizes_reference_p (a : Bool) (o : Fin 4) :
    studentReferenceP (tableSquaredStatistic false 1) 28 ≤
      studentReferenceP (tableSquaredStatistic a o) (if a then 21 else 28) ∧
    normalReferenceP (tableSquaredStatistic false 1) ≤
      normalReferenceP (tableSquaredStatistic a o) := by
  exact AronowAudit.P040.unadjusted_bulk_minimizes_reference_p a o

theorem recorded_statistic_identity (a : Bool) (o : Fin 4) :
    recordedSquaredStatistic a o = tableSquaredStatistic a o := by
  exact AronowAudit.P040.recorded_statistic_identity a o

theorem recorded_df_identity (a : Bool) : recordedResidualDF a = if a then 21 else 28 := by
  exact AronowAudit.P040.recorded_df_identity a

theorem recorded_normal_counterexample :
    roundsTwo (normalReferenceP (recordedSquaredStatistic true 2)) (58 / 100) ∧
    ¬roundsTwo (normalReferenceP (recordedSquaredStatistic true 2)) (59 / 100) ∧
    roundsTwo (normalReferenceP (recordedSquaredStatistic true 1)) (28 / 100) ∧
    ¬roundsTwo (normalReferenceP (recordedSquaredStatistic true 1)) (29 / 100) := by
  exact AronowAudit.P040.recorded_normal_counterexample

theorem recorded_corrected_p_values :
    roundsTwo (studentReferenceP (recordedSquaredStatistic true 2) (recordedResidualDF true)) (59 / 100) ∧
    roundsTwo (studentReferenceP (recordedSquaredStatistic true 1) (recordedResidualDF true)) (29 / 100) := by
  exact AronowAudit.P040.recorded_corrected_p_values

theorem recorded_effects_not_significant (a : Bool) (o : Fin 4) :
    (1 : ℝ) / 10 < studentReferenceP (recordedSquaredStatistic a o) (recordedResidualDF a) ∧
    (1 : ℝ) / 10 < normalReferenceP (recordedSquaredStatistic a o) := by
  exact AronowAudit.P040.recorded_effects_not_significant a o

theorem recorded_table_cells_round :
    saleRoundsOne cafeCoefficientWitness (-89 / 10) ∧
    saleRoundsOne (Real.sqrt cafeVarianceWitness) (162 / 10) ∧
    saleRoundsOne bulkCoefficientWitness (232 / 10) ∧
    saleRoundsOne (Real.sqrt bulkVarianceWitness) (212 / 10) := by
  exact AronowAudit.P040.recorded_table_cells_round

end SAP.P040.Bridge
