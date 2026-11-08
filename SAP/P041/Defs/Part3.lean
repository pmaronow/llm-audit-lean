import SAP.P041.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

/-- Mathematical content packaged for P041-T1. -/
def T1Statement : Prop :=
  (∀ q : ℝ, 0 < q → q < 1 →
      0 < positiveHazard q ∧ 0 < negativeHazard q ∧
      positiveHazard q / negativeHazard q = 2/3 ∧
      negativeHazard q / positiveHazard q = 3/2 ∧ (2/3 : ℝ) ≠ 1 ∧
      exponentialSurvival (positiveHazard q) 12 = q^2 ∧
      exponentialSurvival (negativeHazard q) 12 = q^3 ∧
      twelveHourContrast q = q^2 * (1-q)) ∧
  (∀ q t : ℝ, 0 < q → q < 1 → 0 ≤ t →
      exponentialSurvival (positiveHazard q) t = q^(t/6) ∧
      exponentialSurvival (negativeHazard q) t = q^(t/4)) ∧
  (exponentialSurvival (positiveHazard (4/5)) 12 = 16/25 ∧
    exponentialSurvival (negativeHazard (4/5)) 12 = 64/125 ∧
    twelveHourContrast (4/5) = 16/125 ∧
    exponentialSurvival (positiveHazard (99/100)) 12 = 9801/10000 ∧
    exponentialSurvival (negativeHazard (99/100)) 12 = 970299/1000000 ∧
    twelveHourContrast (99/100) = 9801/1000000 ∧
    twelveHourContrast (4/5) - twelveHourContrast (99/100) = 118199/1000000 ∧
    0 < twelveHourContrast (4/5) - twelveHourContrast (99/100) ∧
    twelveHourContrast (4/5) / twelveHourContrast (99/100) = 128000/9801 ∧
    13 < twelveHourContrast (4/5) / twelveHourContrast (99/100) ∧
    positiveHazard (4/5) / negativeHazard (4/5) = 2/3 ∧
    positiveHazard (99/100) / negativeHazard (99/100) = 2/3 ∧
    (2/3 : ℝ) ≠ 1 ∧
    1 - exponentialSurvival (negativeHazard (4/5)) 12 = 61/125 ∧
    1 - exponentialSurvival (positiveHazard (4/5)) 12 = 9/25 ∧
    1 - exponentialSurvival (negativeHazard (99/100)) 12 = 29701/1000000 ∧
    1 - exponentialSurvival (positiveHazard (99/100)) 12 = 199/10000 ∧
    (0:ℝ) < 61/125 ∧ (61/125 : ℝ) < 1 ∧
    (0:ℝ) < 9/25 ∧ (9/25 : ℝ) < 1 ∧
    (0:ℝ) < 29701/1000000 ∧ (29701/1000000 : ℝ) < 1 ∧
    (0:ℝ) < 199/10000 ∧ (199/10000 : ℝ) < 1 ∧
    0 < binomialCountProbability 150 75 (61/125) ∧
    0 < binomialCountProbability 150 52 (9/25) ∧
    0 < binomialCountProbability 76 1 (29701/1000000) ∧
    0 < binomialCountProbability 75 3 (199/10000))

end SAP.P041
