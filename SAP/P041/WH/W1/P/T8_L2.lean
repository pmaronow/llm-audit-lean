import SAP.P041.WH.W1.Leaves
import AronowAudit.P041.P041_Wald

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P041.WH.W1.P.T8_L2

open SAP.P041.WH.W1
open AronowAudit.P041
open AronowAudit.P041.Wave1
open ProbabilityTheory

lemma log_left :
    (0.735011384 : ℝ) ≤ -Real.log (0.4795 : ℝ) ∧
      -Real.log (0.4795 : ℝ) ≤ 0.735011385 := by
  have hc := neg_log_certificate (0.4795 : ℝ) (by norm_num) (by norm_num) 32
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

lemma log_right :
    (0.732928050 : ℝ) ≤ -Real.log (0.4805 : ℝ) ∧
      -Real.log (0.4805 : ℝ) ≤ 0.732928051 := by
  have hc := neg_log_certificate (0.4805 : ℝ) (by norm_num) (by norm_num) 32
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

lemma abs_hazard_target (h s : ℝ) (h0 : 0 < h) (h1 : h < 1) (hs : 0 < s) :
    |SAP.P041.hazardWald h s| = h * (-Real.log h) / s := by
  simpa [SAP.P041.hazardWald, AronowAudit.P041.hazardWald] using
    AronowAudit.P041.abs_hazard_wald h s h0 h1 hs

end SAP.P041.WH.W1.P.T8_L2

open SAP.P041.WH.W1.P.T8_L2
open AronowAudit.P041.Wave1 ProbabilityTheory

theorem SAP.P041.WH.W1.T8_L2_proof : SAP.P041.WH.W1.T8_L2 := by
  intro h s hh hs
  have hbounds : (0.4795 : ℝ) ≤ h ∧ h ≤ 0.4805 := by
    norm_num [printedInterval] at hh
    exact ⟨by linarith, by linarith⟩
  have sbounds : (0.1735 : ℝ) ≤ s ∧ s ≤ 0.1745 := by
    norm_num [printedInterval] at hs
    exact ⟨by linarith, by linarith⟩
  have h0 : 0 < h := by linarith
  have h1 : h < 1 := by linarith
  have s0 : 0 < s := by linarith
  have hn := AronowAudit.P041.wald_numerator_above (0.4795 : ℝ) (0.4805 : ℝ) h
    (by norm_num) hbounds.1 hbounds.2 (by linarith [log_left.2])
  have hnlo : (0.352171928 : ℝ) ≤ h * (-Real.log h) := by
    have he : (0.352171928 : ℝ) ≤ 0.4805 * (-Real.log (0.4805 : ℝ)) := by
      have hm := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.4805)
        (show (0 : ℝ) ≤ -Real.log (0.4805 : ℝ) - 0.732928050 by linarith [log_right.1])
      nlinarith
    linarith
  have hnhi : h * (-Real.log h) ≤ (0.352437960 : ℝ) := by
    have he : 0.4795 * (-Real.log (0.4795 : ℝ)) ≤ (0.352437960 : ℝ) := by
      have hm := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.4795)
        (show (0 : ℝ) ≤ 0.735011385 - (-Real.log (0.4795 : ℝ)) by linarith [log_left.2])
      nlinarith
    linarith
  have hzlo : (2.0181 : ℝ) ≤ |hazardWald h s| := by
    rw [abs_hazard_target h s h0 h1 s0]
    apply (le_div_iff₀ s0).2
    have hp := mul_le_mul_of_nonneg_left sbounds.2 (by norm_num : (0 : ℝ) ≤ 2.0181)
    nlinarith
  have hzhi : |hazardWald h s| ≤ (2.0314 : ℝ) := by
    rw [abs_hazard_target h s h0 h1 s0]
    apply (div_le_iff₀ s0).2
    have hp := mul_le_mul_of_nonneg_left sbounds.1 (by norm_num : (0 : ℝ) ≤ 2.0314)
    nlinarith
  have ht_hi := normal_tail_fine 14 (2.0314 : ℝ) (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have ht_lo := normal_tail_fine 14 (2.0181 : ℝ) (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial] at ht_hi ht_lo
  refine ⟨h0, h1, s0, hzlo, hzhi, ?_, ?_⟩
  · change (0.041792640 : ℝ) ≤
      2 * cdf (gaussianReal 0 1) (-|hazardWald h s|)
    have hm := normal_tail_antitone hzhi
    linarith
  · change 2 * cdf (gaussianReal 0 1) (-|hazardWald h s|) ≤
      (0.044011941 : ℝ)
    have hm := normal_tail_antitone hzlo
    linarith

