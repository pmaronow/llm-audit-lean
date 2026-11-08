import SAP.P040.Defs.Part2
import SAP.P040.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P040
open scoped BigOperators
open MeasureTheory
noncomputable section

/-- The normal-reference rounding mismatch on the actual adjusted regressions. -/
def normalRoundingMismatch : Prop :=
    roundsTwo (normalReferenceP (recordedSquaredStatistic true 2)) (58 / 100) ∧
    ¬ roundsTwo (normalReferenceP (recordedSquaredStatistic true 2)) (59 / 100) ∧
    roundsTwo (normalReferenceP (recordedSquaredStatistic true 1)) (28 / 100) ∧
    ¬ roundsTwo (normalReferenceP (recordedSquaredStatistic true 1)) (29 / 100)

/-- The observed adjusted cafe and bulk statistics, with both printed reference calculations. -/
def T4Statement : Prop :=
    Function.Injective adjustedDesign.mulVecLin ∧
    adjustedDesign.rank = 9 ∧ originalAdjustedDesign.rank = 9 ∧
    recordedResidualDF true = 21 ∧
    olsCoefficients adjustedDesign salesCafe 1 = cafeCoefficientWitness ∧
    hc1Variance adjustedDesign salesCafe 1 = cafeVarianceWitness ∧
    olsCoefficients adjustedDesign salesBulk 1 = bulkCoefficientWitness ∧
    hc1Variance adjustedDesign salesBulk 1 = bulkVarianceWitness ∧
    0 < cafeVarianceWitness ∧ 0 < bulkVarianceWitness ∧
    cafeCoefficientWitness ^ 2 / cafeVarianceWitness = cafeSquaredStatistic ∧
    bulkCoefficientWitness ^ 2 / bulkVarianceWitness = bulkSquaredStatistic ∧
    recordedSquaredStatistic true 2 = cafeSquaredStatistic ∧
    recordedSquaredStatistic true 1 = bulkSquaredStatistic ∧
    0 < cafeSquaredStatistic ∧ cafeSquaredStatistic < (8 : ℝ) / 5 ∧
    0 < bulkSquaredStatistic ∧ bulkSquaredStatistic < (8 : ℝ) / 5 ∧
    saleRoundsOne cafeCoefficientWitness (-89 / 10) ∧
    saleRoundsOne (Real.sqrt cafeVarianceWitness) (162 / 10) ∧
    saleRoundsOne bulkCoefficientWitness (232 / 10) ∧
    saleRoundsOne (Real.sqrt bulkVarianceWitness) (212 / 10) ∧
    roundsSix cafeCoefficientWitness (-8891107 / 1000000) ∧
    roundsSix (Real.sqrt cafeVarianceWitness) (16151244 / 1000000) ∧
    roundsSix cafeSquaredStatistic (303040 / 1000000) ∧
    roundsSix (Real.sqrt cafeSquaredStatistic) (550491 / 1000000) ∧
    roundsSix bulkCoefficientWitness (23178816 / 1000000) ∧
    roundsSix (Real.sqrt bulkVarianceWitness) (21247014 / 1000000) ∧
    roundsSix bulkSquaredStatistic (1190109 / 1000000) ∧
    roundsSix (Real.sqrt bulkSquaredStatistic) (1090921 / 1000000) ∧
    (58198 / 100000 : ℝ) < normalReferenceP (recordedSquaredStatistic true 2) ∧
    normalReferenceP (recordedSquaredStatistic true 2) < (58199 / 100000 : ℝ) ∧
    (27530 / 100000 : ℝ) < normalReferenceP (recordedSquaredStatistic true 1) ∧
    normalReferenceP (recordedSquaredStatistic true 1) < (27531 / 100000 : ℝ) ∧
    normalRoundingMismatch ∧
    roundsTwo (studentReferenceP (recordedSquaredStatistic true 2) 21) (59 / 100) ∧
    roundsTwo (studentReferenceP (recordedSquaredStatistic true 1) 21) (29 / 100)

/-- The corrected Student-t reference, all eight fitted statistics, and the normal alternative. -/
def T5Statement : Prop :=
    Fintype.card (Fin 30) = 30 ∧
    unadjustedDesign.rank = 2 ∧ adjustedDesign.rank = 9 ∧ originalAdjustedDesign.rank = 9 ∧
    Function.Injective unadjustedDesign.mulVecLin ∧
    Function.Injective adjustedDesign.mulVecLin ∧
    (∀ i : Fin 30, (∑ c : Fin 7, centeredWeekday c i) = 0) ∧
    LinearMap.range originalAdjustedDesign.mulVecLin = LinearMap.range adjustedDesign.mulVecLin ∧
    (∀ a : Bool, recordedResidualDF a = if a then 21 else 28) ∧
    (∀ t : ℝ, studentReferenceDensity 21 t = student21Density t) ∧
    (58779 / 100000 : ℝ) < studentReferenceP (recordedSquaredStatistic true 2) 21 ∧
    studentReferenceP (recordedSquaredStatistic true 2) 21 < (58780 / 100000 : ℝ) ∧
    (28766 / 100000 : ℝ) < studentReferenceP (recordedSquaredStatistic true 1) 21 ∧
    studentReferenceP (recordedSquaredStatistic true 1) 21 < (28767 / 100000 : ℝ) ∧
    roundsTwo (studentReferenceP (recordedSquaredStatistic true 2) (recordedResidualDF true)) (59 / 100) ∧
    roundsTwo (studentReferenceP (recordedSquaredStatistic true 1) (recordedResidualDF true)) (29 / 100) ∧
    (∀ a : Bool, ∀ o : Fin 4,
      recordedSquaredStatistic a o = tableSquaredStatistic a o ∧
      0 < recordedSquaredStatistic a o ∧
      recordedSquaredStatistic a o ≤ recordedSquaredStatistic false 1 ∧
      (1 : ℝ) / 10 < studentReferenceP (recordedSquaredStatistic a o) (recordedResidualDF a) ∧
      (1 : ℝ) / 10 < normalReferenceP (recordedSquaredStatistic a o) ∧
      studentReferenceP (recordedSquaredStatistic false 1) 28 ≤
        studentReferenceP (recordedSquaredStatistic a o) (recordedResidualDF a) ∧
      normalReferenceP (recordedSquaredStatistic false 1) ≤
        normalReferenceP (recordedSquaredStatistic a o)) ∧
    recordedSquaredStatistic false 1 < (8 : ℝ) / 5 ∧
    (22533 / 100000 : ℝ) < studentReferenceP (recordedSquaredStatistic false 1) 28 ∧
    studentReferenceP (recordedSquaredStatistic false 1) 28 < (22534 / 100000 : ℝ) ∧
    (21504 / 100000 : ℝ) < normalReferenceP (recordedSquaredStatistic false 1) ∧
    normalReferenceP (recordedSquaredStatistic false 1) < (21505 / 100000 : ℝ) ∧
    normalRoundingMismatch

end
end SAP.P040
