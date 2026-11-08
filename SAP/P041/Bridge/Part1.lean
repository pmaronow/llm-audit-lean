import SAP.P041.Defs
import AronowAudit.P041.P041_Hazards
import AronowAudit.P041.P041_OLS
import AronowAudit.P041.P041_Order
import AronowAudit.P041.P041_PrintedRefutations
import AronowAudit.P041.P041_Risks
import AronowAudit.P041.P041_Tenure
import AronowAudit.P041.P041_Wald
import AronowAudit.P041.Wave1.Gap.GLP041P042P045B1
import AronowAudit.P041.Wave1.Gap.GP041P042P045B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.Bridge
open Matrix
open scoped BigOperators

theorem common_bias_countermodel :
  exponentialSurvival (positiveHazard (4/5)) 12 = 16/25 ∧
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
    0 < binomialCountProbability 75 3 (199/10000) := by
  exact @AronowAudit.P041.common_bias_countermodel

theorem proportional_hazards :
  ∀ (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1),
    0 < positiveHazard q ∧ 0 < negativeHazard q ∧
    positiveHazard q / negativeHazard q = 2/3 ∧
    negativeHazard q / positiveHazard q = 3/2 ∧
    (2/3 : ℝ) ≠ 1 := by
  exact @AronowAudit.P041.proportional_hazards

theorem corrected_normal_p_approximations_proof :
  |normalTwoSided (hazardWald 0.691 0.318) - 0.42| ≤ 0.005 ∧
    |normalTwoSided (betweenHazardWald 0.691 0.318 0.629 0.091) - 0.845| ≤ 0.0005 := by
  exact @AronowAudit.P041.Wave1.corrected_normal_p_approximations_proof

theorem corrected_between_relative_effects :
  ∀ (hF sF hA sA : ℝ)
    (hf : printedInterval 0.691 hF) (sf : printedInterval 0.318 sF)
    (ha : printedInterval 0.629 hA) (sa : printedInterval 0.091 sA),
    0.18 < betweenHazardWald hF sF hA sA ∧ betweenHazardWald hF sF hA sA < 0.21 := by
  exact @AronowAudit.P041.corrected_between_relative_effects

theorem corrected_former_imprecision :
  ∀ (hF sF hA sA : ℝ)
    (hf : printedInterval 0.691 hF) (sf : printedInterval 0.318 sF)
    (ha : printedInterval 0.629 hA) (sa : printedInterval 0.091 sA),
    |Real.log hF - Real.log hA| < 0.21 * logHazardSE hF sF ∧
    0.21 * logHazardSE hF sF < (49/25) * logHazardSE hF sF ∧
    |Real.log hF| < (49/25) * logHazardSE hF sF ∧
    1 ∈ hazardWaldInterval hF sF ∧ hA ∈ hazardWaldInterval hF sF := by
  exact @AronowAudit.P041.corrected_former_imprecision

theorem corrected_former_nondetection :
  ∀ (h s : ℝ)
    (hh : printedInterval 0.691 h) (hs : printedInterval 0.318 s),
    0.80 < |hazardWald h s| ∧ |hazardWald h s| < 0.81 ∧ |hazardWald h s| < 1 := by
  exact @AronowAudit.P041.corrected_former_nondetection

theorem former_wald_endpoint_enclosures :
  ∀ (h s : ℝ)
    (hh : printedInterval 0.691 h) (hs : printedInterval 0.318 s),
    0.279 < Real.exp (Real.log h-(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h-(49/25)*logHazardSE h s) < 0.282 ∧
    1.700 < Real.exp (Real.log h+(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h+(49/25)*logHazardSE h s) < 1.706 := by
  exact @AronowAudit.P041.former_wald_endpoint_enclosures

theorem observed_early_contrasts :
  observedSurvivalContrast 150 150 52 75 = 23/150 ∧
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
      observedSurvivalContrast 75 76 7 3 := by
  exact @AronowAudit.P041.observed_early_contrasts

theorem smaller_contrast_does_not_exclude_common_bias :
  ∃ qA qF : ℝ, 0 < qA ∧ qA < 1 ∧ 0 < qF ∧ qF < 1 ∧
      positiveHazard qA / negativeHazard qA = 2/3 ∧
      positiveHazard qF / negativeHazard qF = 2/3 ∧
      positiveHazard qF / negativeHazard qF ≠ 1 ∧
      0 < twelveHourContrast qF ∧
      13 * twelveHourContrast qF < twelveHourContrast qA := by
  exact @AronowAudit.P041.smaller_contrast_does_not_exclude_common_bias

theorem corrected_normal_star_tiers_proof :
  (∀ h s : ℝ, printedInterval 0.670 h → printedInterval 0.095 s →
      normalTwoSided (hazardWald h s) < 0.01 ∧ significanceTier (hazardWald h s) = 3) ∧
    (∀ h s : ℝ, printedInterval 0.480 h → printedInterval 0.174 s →
      0.01 < normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.05 ∧
      significanceTier (hazardWald h s) = 2) ∧
    (∀ h s : ℝ, printedInterval 0.274 h → printedInterval 0.162 s →
      0.01 < normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.05 ∧
      significanceTier (hazardWald h s) = 2) ∧
    (∀ h s : ℝ, printedInterval 0.316 h → printedInterval 0.149 s →
      0.01 < normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.05 ∧
      significanceTier (hazardWald h s) = 2) := by
  exact @AronowAudit.P041.Wave1.corrected_normal_star_tiers_proof

theorem corrected_star_wald_bounds :
  (∀ h s : ℝ, printedInterval 0.670 h → printedInterval 0.095 s →
      2.80 < |hazardWald h s|) ∧
    (∀ h s : ℝ, printedInterval 0.480 h → printedInterval 0.174 s →
      2.01 < |hazardWald h s| ∧ |hazardWald h s| < 2.04) ∧
    (∀ h s : ℝ, printedInterval 0.274 h → printedInterval 0.162 s →
      2.18 < |hazardWald h s| ∧ |hazardWald h s| < 2.20) ∧
    (∀ h s : ℝ, printedInterval 0.316 h → printedInterval 0.149 s →
      2.43 < |hazardWald h s| ∧ |hazardWald h s| < 2.46) := by
  exact @AronowAudit.P041.corrected_star_wald_bounds

theorem former_two_group_slope :
  ∀ (β : Fin 2 → ℝ) (sT sB : ℝ)
    (hβ : (!![151,75;75,75] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ β = ![sT+sB,sT]),
    β 1 = sT/75 - sB/76 := by
  exact @AronowAudit.P041.former_two_group_slope

theorem ols_normal_equations :
  ∀ {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (X : Matrix n k ℝ) (y : n → ℝ) (hX : IsUnit (X.transpose * X).det),
    (X.transpose * X) *ᵥ olsCoefficients X y = X.transpose *ᵥ y := by
  exact @AronowAudit.P041.ols_normal_equations

theorem reciprocal_standard_error_and_wald :
  ∀ (g V s : ℝ) (_hV : 0 ≤ V)
    (hs : s = Real.exp g * Real.sqrt V),
    (1/Real.exp g) * Real.sqrt V = s/(Real.exp g)^2 ∧ (-g)^2/V = g^2/V := by
  exact @AronowAudit.P041.reciprocal_standard_error_and_wald

theorem printed_former_normal_p_enclosures_proof :
  (∀ h s : ℝ, printedInterval 0.691 h → printedInterval 0.318 s →
      0.4205 ≤ normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) ≤ 0.4232) ∧
    (∀ h s : ℝ, printedInterval 0.775 h → printedInterval 0.503 s →
      0.6936 ≤ normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) ≤ 0.6954) ∧
    (∀ h s : ℝ, printedInterval 0.627 h → printedInterval 0.406 s →
      0.4700 ≤ normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) ≤ 0.4720) ∧
    abs (abs (hazardWald 0.691 0.318) - 0.8032) ≤ 0.00005 ∧
    abs (abs (hazardWald 0.775 0.503) - 0.3927) ≤ 0.00005 ∧
    abs (abs (hazardWald 0.627 0.406) - 0.7209) ≤ 0.00005 ∧
    |normalTwoSided (hazardWald 0.691 0.318) - 0.4219| ≤ 0.00005 ∧
    |normalTwoSided (hazardWald 0.775 0.503) - 0.6945| ≤ 0.00005 ∧
    |normalTwoSided (hazardWald 0.627 0.406) - 0.4710| ≤ 0.00005 := by
  exact @AronowAudit.P041.Wave1.printed_former_normal_p_enclosures_proof

theorem former_subgroup_nondetections :
  (∀ h s : ℝ, printedInterval 0.691 h → printedInterval 0.318 s → |hazardWald h s| < 1) ∧
    (∀ h s : ℝ, printedInterval 0.775 h → printedInterval 0.503 s → |hazardWald h s| < 1) ∧
    (∀ h s : ℝ, printedInterval 0.627 h → printedInterval 0.406 s → |hazardWald h s| < 1) := by
  exact @AronowAudit.P041.former_subgroup_nondetections

end SAP.P041.Bridge
