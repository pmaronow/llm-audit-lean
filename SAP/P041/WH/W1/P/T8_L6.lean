import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W1.P.T8_L6

open MeasureTheory ProbabilityTheory
open AronowAudit.P041
open AronowAudit.P041.Wave1

private def centreLower : ℝ := 404948510389 / 200000000000
private def centreUpper : ℝ := 1012371275973 / 500000000000

lemma centre_magnitude :
    centreLower ≤ |hazardWald (0.480 : ℝ) (0.174 : ℝ)| ∧
      |hazardWald (0.480 : ℝ) (0.174 : ℝ)| ≤ centreUpper := by
  have habs : |hazardWald (0.480 : ℝ) (0.174 : ℝ)| =
      (0.480 : ℝ) * (-Real.log (0.480 : ℝ)) / (0.174 : ℝ) :=
    AronowAudit.P041.abs_hazard_wald _ _ (by norm_num) (by norm_num) (by norm_num)
  rw [habs]
  have hc := neg_log_certificate (0.480 : ℝ) (by norm_num) (by norm_num) 14
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor
  · apply (le_div_iff₀ (by norm_num : (0:ℝ) < 0.174)).mpr
    dsimp [centreLower]
    nlinarith [hc.1]
  · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 0.174)).mpr
    dsimp [centreUpper]
    nlinarith [hc.2]

lemma centre_negative : hazardWald (0.480 : ℝ) (0.174 : ℝ) < 0 := by
  unfold hazardWald
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (by norm_num) (Real.log_neg (by norm_num) (by norm_num)))
    (by norm_num)

lemma centre_statistic_error :
    |hazardWald (0.480 : ℝ) (0.174 : ℝ) - (-2.02474)| < 0.00001 := by
  have hm := centre_magnitude
  have hn := centre_negative
  have habs : |hazardWald (0.480 : ℝ) (0.174 : ℝ)| = -hazardWald (0.480 : ℝ) (0.174 : ℝ) := abs_of_neg hn
  rw [abs_lt]
  constructor <;> dsimp [centreLower, centreUpper] at hm <;> linarith [hm.1, hm.2, habs]

lemma centre_tail_bound :
    0.04289380 ≤ normalTwoSided (hazardWald (0.480 : ℝ) (0.174 : ℝ)) ∧
      normalTwoSided (hazardWald (0.480 : ℝ) (0.174 : ℝ)) ≤ 0.04289381 := by
  have hm := centre_magnitude
  have ha : 0 ≤ centreLower := by norm_num [centreLower]
  have hb : 0 ≤ centreUpper := by norm_num [centreUpper]
  have hpa : 0 ≤ normal_intPoly 29 centreLower := by
    norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial, centreLower]
  have hpb : 0 ≤ normal_intPoly 29 centreUpper := by
    norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial, centreUpper]
  have ta := normal_tail_fine 14 centreLower ha hpa
  have tb := normal_tail_fine 14 centreUpper hb hpb
  have hlow : (0.04289380 : ℝ) ≤ 1 - 2*0.39894228040143269*normal_intPoly 28 centreUpper := by
    norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial, centreUpper]
  have hupp : 1 - 2*0.39894228040143267*normal_intPoly 29 centreLower ≤ (0.04289381 : ℝ) := by
    norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial, centreLower]
  have hactual : centreLower ≤ |hazardWald (0.480 : ℝ) (0.174 : ℝ)| ∧
      |hazardWald (0.480 : ℝ) (0.174 : ℝ)| ≤ centreUpper := hm
  have hl : (0.04289380 : ℝ) ≤ 2*cdf (gaussianReal 0 1) (-|hazardWald (0.480 : ℝ) (0.174 : ℝ)|) := by
    exact le_trans hlow (le_trans tb.1 (normal_tail_antitone hactual.2))
  have hu : 2*cdf (gaussianReal 0 1) (-|hazardWald (0.480 : ℝ) (0.174 : ℝ)|) ≤ (0.04289381 : ℝ) := by
    exact le_trans (normal_tail_antitone hactual.1) (le_trans ta.2 hupp)
  simpa [normalTwoSided] using And.intro hl hu

end SAP.P041.WH.W1.P.T8_L6

theorem SAP.P041.WH.W1.T8_L6_proof : SAP.P041.WH.W1.T8_L6 := by
  refine ⟨SAP.P041.WH.W1.P.T8_L6.centre_negative, ?_, ?_⟩
  · exact SAP.P041.WH.W1.P.T8_L6.centre_statistic_error
  · have hp := SAP.P041.WH.W1.P.T8_L6.centre_tail_bound
    rw [abs_lt]
    constructor <;> linarith [hp.1, hp.2]
