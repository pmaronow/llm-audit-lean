import SAP.P040.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P040
open scoped BigOperators
open MeasureTheory
noncomputable section

def normalReferenceP (q : ℝ) : ℝ :=
  1 - Real.sqrt (2 / Real.pi) * ∫ u in (0 : ℝ)..Real.sqrt q, Real.exp (-u ^ 2 / 2)

def studentReferenceDensity (nu t : ℝ) : ℝ :=
  Real.Gamma ((nu + 1) / 2) / (Real.sqrt (nu * Real.pi) * Real.Gamma (nu / 2)) *
    (1 + t ^ 2 / nu) ^ (-((nu + 1) / 2))

def studentReferenceP (q nu : ℝ) : ℝ :=
  1 - 2 * ∫ t in (0 : ℝ)..Real.sqrt q, studentReferenceDensity nu t

def cafeSquaredStatistic : ℝ := 12767624825803755635000 / 42131842162249950707521

def bulkSquaredStatistic : ℝ := 12396039010057804992800 / 10415886991743115636339

def cafeCoefficientWitness : ℝ := -146561 / 16484

def cafeVarianceWitness : ℝ := 42131842162249950707521 / 161509653387533360000

def bulkCoefficientWitness : ℝ := 955199 / 41210

def bulkVarianceWitness : ℝ := 10415886991743115636339 / 23072807626790480000

def student21Density (t : ℝ) : ℝ :=
  (4 : ℝ) ^ 10 / (Real.pi * (Nat.choose 20 10 : ℝ) * Real.sqrt 21) /
    (1 + t ^ 2 / 21) ^ 11

def salesDay : Fin 30 → ℕ :=
  ![1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

def salesTreatment : Fin 30 → ℝ :=
  ![0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1]

def salesBook : Fin 30 → ℝ :=
  ![18171 / 100, 2687 / 20, 3271 / 20, 1713 / 20, 1419 / 10, 171, 1199 / 10, 1338 / 5, 5803 / 20, 168, 4981 / 20, 4511 / 20, 1293 / 10, 982 / 5, 801 / 4, 10589 / 25, 739 / 4, 3573 / 20, 839 / 10, 2647 / 20, 2241 / 20, 2413 / 20, 9019 / 20, 523 / 4, 387 / 4, 1679 / 10, 719 / 5, 200, 443 / 5, 738 / 5]

def salesCafe : Fin 30 → ℝ :=
  ![9838 / 25, 36757 / 100, 5867 / 20, 5048 / 25, 29321 / 100, 30503 / 100, 10524 / 25, 7572 / 25, 38119 / 100, 5051 / 20, 29613 / 100, 8559 / 20, 8971 / 25, 34107 / 100, 16459 / 50, 7773 / 25, 24609 / 100, 31499 / 100, 6391 / 20, 36247 / 100, 389, 16343 / 50, 40049 / 100, 233, 359, 329, 349, 10711 / 25, 33407 / 100, 286]

def salesBulk : Fin 30 → ℝ :=
  ![421 / 5, 1623 / 20, 2001 / 20, 341 / 20, 10271 / 100, 6919 / 100, 1963 / 20, 3207 / 20, 17251 / 100, 99 / 5, 5549 / 100, 18031 / 100, 4008 / 25, 2899 / 50, 4051 / 50, 647 / 20, 2541 / 50, 154 / 5, 3059 / 25, 1247 / 25, 3831 / 50, 849 / 20, 1517 / 10, 1261 / 20, 12013 / 100, 381 / 20, 5991 / 100, 2853 / 25, 2497 / 100, 2703 / 25]

def salesTotal (i : Fin 30) : ℝ := salesBook i + salesCafe i + salesBulk i

def tableOutcome : Fin 4 → Fin 30 → ℝ := ![salesTotal, salesBulk, salesCafe, salesBook]

def meanSalesDay : ℝ := (∑ i : Fin 30, (salesDay i : ℝ)) / 30

def weekdayFrequency (c : Fin 7) : ℝ :=
  (∑ i : Fin 30, if salesDay i % 7 = c.val then (1 : ℝ) else 0) / 30

def centeredWeekday (c : Fin 7) (i : Fin 30) : ℝ :=
  (if salesDay i % 7 = c.val then (1 : ℝ) else 0) - weekdayFrequency c

def unadjustedDesign : Matrix (Fin 30) (Fin 2) ℝ :=
  fun i => ![1, salesTreatment i]

def adjustedDesign : Matrix (Fin 30) (Fin 9) ℝ :=
  fun i => ![1, salesTreatment i, (salesDay i : ℝ) - meanSalesDay,
    centeredWeekday 0 i, centeredWeekday 1 i, centeredWeekday 2 i,
    centeredWeekday 3 i, centeredWeekday 4 i, centeredWeekday 5 i]

def originalAdjustedDesign : Matrix (Fin 30) (Fin 10) ℝ :=
  fun i => ![1, salesTreatment i, (salesDay i : ℝ) - meanSalesDay,
    centeredWeekday 0 i, centeredWeekday 1 i, centeredWeekday 2 i,
    centeredWeekday 3 i, centeredWeekday 4 i, centeredWeekday 5 i, centeredWeekday 6 i]

def olsOperator {K : ℕ} (X : Matrix (Fin 30) (Fin K) ℝ) : Matrix (Fin K) (Fin 30) ℝ :=
  (X.transpose * X)⁻¹ * X.transpose

def olsCoefficients {K : ℕ} (X : Matrix (Fin 30) (Fin K) ℝ) (y : Fin 30 → ℝ) : Fin K → ℝ :=
  (olsOperator X).mulVec y

def olsResidual {K : ℕ} (X : Matrix (Fin 30) (Fin K) ℝ) (y : Fin 30 → ℝ) (i : Fin 30) : ℝ :=
  y i - X.mulVec (olsCoefficients X y) i

def hc1Variance {K : ℕ} (X : Matrix (Fin 30) (Fin K) ℝ) (y : Fin 30 → ℝ) (t : Fin K) : ℝ :=
  (30 : ℝ) / (30 - (K : ℝ)) *
    ∑ i : Fin 30, (olsOperator X t i * olsResidual X y i) ^ 2

def olsSquaredStatistic {K : ℕ} (X : Matrix (Fin 30) (Fin K) ℝ)
    (y : Fin 30 → ℝ) (t : Fin K) : ℝ := olsCoefficients X y t ^ 2 / hc1Variance X y t

def tableSquaredStatistic (adjusted : Bool) : Fin 4 → ℝ :=
  if adjusted then ![1200277903320876335774 / 280628848000463708694463,
    bulkSquaredStatistic, cafeSquaredStatistic, 3084161273413343448962 / 24391999904970062376441]
  else ![263679812816672 / 522999591200175, 23273498735648 / 15141092298015,
    1492978176032 / 21949506186495, 9067019347232 / 22381571766655]

def recordedSquaredStatistic (a : Bool) (o : Fin 4) : ℝ :=
  if a then olsSquaredStatistic adjustedDesign (tableOutcome o) 1
  else olsSquaredStatistic unadjustedDesign (tableOutcome o) 1

def recordedResidualDF (a : Bool) : ℝ :=
  if a then (30 - originalAdjustedDesign.rank : ℕ) else (30 - unadjustedDesign.rank : ℕ)

def saleRoundsOne (x w : ℝ) : Prop := w - 1 / 20 ≤ x ∧ x < w + 1 / 20


end
end SAP.P040
