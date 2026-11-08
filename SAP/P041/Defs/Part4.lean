import SAP.P041.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

/-- Mathematical content packaged for P041-T2. -/
def T2Statement : Prop :=
  (∀ (h s : ℝ)
    (hh : printedInterval 0.691 h) (hs : printedInterval 0.318 s),
    0.80 < |hazardWald h s| ∧ |hazardWald h s| < 0.81 ∧ |hazardWald h s| < 1) ∧
  (∀ (hF sF hA sA : ℝ)
    (hf : printedInterval 0.691 hF) (sf : printedInterval 0.318 sF)
    (ha : printedInterval 0.629 hA) (sa : printedInterval 0.091 sA),
    |Real.log hF - Real.log hA| < 0.21 * logHazardSE hF sF ∧
    0.21 * logHazardSE hF sF < (49/25) * logHazardSE hF sF ∧
    |Real.log hF| < (49/25) * logHazardSE hF sF ∧
    1 ∈ hazardWaldInterval hF sF ∧ hA ∈ hazardWaldInterval hF sF) ∧
  (∀ (h s : ℝ)
    (hh : printedInterval 0.691 h) (hs : printedInterval 0.318 s),
    0.279 < Real.exp (Real.log h-(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h-(49/25)*logHazardSE h s) < 0.282 ∧
    1.700 < Real.exp (Real.log h+(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h+(49/25)*logHazardSE h s) < 1.706) ∧
  (∀ (hF sF hA sA : ℝ)
    (hf : printedInterval 0.691 hF) (sf : printedInterval 0.318 sF)
    (ha : printedInterval 0.629 hA) (sa : printedInterval 0.091 sA),
    0.18 < betweenHazardWald hF sF hA sA ∧ betweenHazardWald hF sF hA sA < 0.21) ∧
  (|normalTwoSided (hazardWald 0.691 0.318) - 0.42| ≤ 0.005 ∧
    |normalTwoSided (betweenHazardWald 0.691 0.318 0.629 0.091) - 0.845| ≤ 0.0005) ∧
  (observedSurvivalContrast 150 150 52 75 = 23/150 ∧
    observedSurvivalContrast 75 76 3 1 = -51/1900 ∧
    observedSurvivalContrast 150 150 52 75 -
      observedSurvivalContrast 75 76 3 1 = 1027/5700 ∧
    0 < observedSurvivalContrast 150 150 52 75 -
      observedSurvivalContrast 75 76 3 1 ∧
    observedSurvivalContrast 150 150 82 101 = 19/150 ∧
    observedSurvivalContrast 75 76 7 3 = -307/5700 ∧
    observedSurvivalContrast 150 150 82 101 -
      observedSurvivalContrast 75 76 7 3 = 343/1900 ∧
    0 < observedSurvivalContrast 150 150 82 101 -
      observedSurvivalContrast 75 76 7 3) ∧
  (∃ qA qF : ℝ, 0 < qA ∧ qA < 1 ∧ 0 < qF ∧ qF < 1 ∧
      positiveHazard qA / negativeHazard qA = 2/3 ∧
      positiveHazard qF / negativeHazard qF = 2/3 ∧
      positiveHazard qF / negativeHazard qF ≠ 1 ∧
      0 < twelveHourContrast qF ∧
      13 * twelveHourContrast qF < twelveHourContrast qA)

end SAP.P041
