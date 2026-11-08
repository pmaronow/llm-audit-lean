import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W1.P.T8_L5

open ProbabilityTheory
open AronowAudit.P041
open AronowAudit.P041.Wave1

theorem centre_stat_negative :
    hazardWald (0.670 : ℝ) 0.095 < 0 := by
  unfold hazardWald
  have hlog : Real.log (0.670 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_pos_of_neg (by norm_num) hlog
  · norm_num

theorem centre_abs_bracket :
    (2.824420732842 : ℝ) ≤ |hazardWald (0.670 : ℝ) 0.095| ∧
      |hazardWald (0.670 : ℝ) 0.095| ≤ 2.824420732843 := by
  have hl := neg_log_certificate (0.670 : ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hl
  have hw := abs_hazard_wald (0.670 : ℝ) 0.095 (by norm_num) (by norm_num) (by norm_num)
  constructor
  · calc
      (2.824420732842 : ℝ) ≤ 0.670 * -Real.log 0.670 / 0.095 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 0.095)).2
        nlinarith [hl.1]
      _ = |hazardWald (0.670 : ℝ) 0.095| := hw.symm
  · calc
      |hazardWald (0.670 : ℝ) 0.095| = 0.670 * -Real.log 0.670 / 0.095 := hw
      _ ≤ 2.824420732843 := by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 0.095)).2
        nlinarith [hl.2]

theorem normal_tail_endpoint_bounds :
    (0.00473661 : ℝ) ≤ 2*cdf (gaussianReal 0 1) (-2.824420732843) ∧
      2*cdf (gaussianReal 0 1) (-2.824420732842) ≤ 0.00473662 := by
  have hlo := normal_tail_fine 14 (2.824420732842 : ℝ) (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have hhi := normal_tail_fine 14 (2.824420732843 : ℝ) (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial] at hlo hhi
  exact ⟨by linarith [hhi.1], by linarith [hlo.2]⟩

end SAP.P041.WH.W1.P.T8_L5

open ProbabilityTheory
open AronowAudit.P041
open AronowAudit.P041.Wave1

theorem SAP.P041.WH.W1.T8_L5_proof : SAP.P041.WH.W1.T8_L5 := by
  refine ⟨SAP.P041.WH.W1.P.T8_L5.centre_stat_negative, ?_, ?_⟩
  · have hneg := SAP.P041.WH.W1.P.T8_L5.centre_stat_negative
    have habs := SAP.P041.WH.W1.P.T8_L5.centre_abs_bracket
    have hstat : hazardWald (0.670 : ℝ) 0.095 = -|hazardWald 0.670 0.095| := by
      rw [abs_of_nonpos hneg.le]
      ring
    rw [hstat]
    apply abs_lt.mpr
    constructor <;> linarith [habs.1, habs.2]
  · have habs := SAP.P041.WH.W1.P.T8_L5.centre_abs_bracket
    have hend := SAP.P041.WH.W1.P.T8_L5.normal_tail_endpoint_bounds
    have hlow := normal_tail_antitone habs.2
    have hhigh := normal_tail_antitone habs.1
    unfold normalTwoSided
    apply abs_lt.mpr
    constructor <;> linarith [hend.1, hend.2, hlow, hhigh]

