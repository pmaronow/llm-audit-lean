import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W1.P.T8_L3

open AronowAudit.P041
open AronowAudit.P041.Wave1
open ProbabilityTheory

lemma log_lower_endpoint :
    (1.2964535 : ℝ) < -Real.log (547/2000 : ℝ) ∧
      -Real.log (547/2000 : ℝ) < 1.2964560 := by
  have hc := neg_log_certificate (547/2000 : ℝ) (by norm_num) (by norm_num) 12
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

lemma log_upper_endpoint :
    (1.2928039 : ℝ) < -Real.log (549/2000 : ℝ) ∧
      -Real.log (549/2000 : ℝ) < 1.2928063 := by
  have hc := neg_log_certificate (549/2000 : ℝ) (by norm_num) (by norm_num) 12
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

lemma wald_bounds (h s : ℝ)
    (hh : printedInterval 0.274 h) (hs : printedInterval 0.162 s) :
    0 < h ∧ h < 1 ∧ 0 < s ∧
      (2.1820 : ℝ) ≤ |hazardWald h s| ∧
      |hazardWald h s| ≤ 2.1974 := by
  rcases hh with ⟨hlo, hhi⟩
  rcases hs with ⟨slo, shi⟩
  have hpos : 0 < h := by linarith
  have hlt : h < 1 := by linarith
  have spos : 0 < s := by linarith
  have hlogL := log_lower_endpoint
  have hlogU := log_upper_endpoint
  have hn := wald_numerator_below (547/2000 : ℝ) (549/2000 : ℝ) h
    (by norm_num) (by linarith) (by linarith)
    (by linarith [hlogU.1])
  have habs : |SAP.P041.hazardWald h s| = h * (-Real.log h) / s := by
    change |AronowAudit.P041.hazardWald h s| = h * (-Real.log h) / s
    exact abs_hazard_wald h s hpos hlt spos
  refine ⟨hpos, hlt, spos, ?_, ?_⟩
  · rw [habs]
    apply (le_div_iff₀ spos).2
    have hbaseL : (547/2000 : ℝ) * 1.2964535 ≤
        (547/2000 : ℝ) * (-Real.log (547/2000 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogL.1.le (by norm_num)
    have hnL : (547/2000 : ℝ) * 1.2964535 ≤ h * (-Real.log h) := by
      exact le_trans hbaseL hn.1
    nlinarith [hnL]
  · rw [habs]
    apply (div_le_iff₀ spos).2
    have hbaseU : (549/2000 : ℝ) * (-Real.log (549/2000 : ℝ)) ≤
        (549/2000 : ℝ) * 1.2928063 :=
      mul_le_mul_of_nonneg_left hlogU.2.le (by norm_num)
    have hnU : h * (-Real.log h) ≤ (549/2000 : ℝ) * 1.2928063 :=
      le_trans hn.2 hbaseU
    nlinarith [hnU]

lemma normal_endpoint_bounds :
    (0.027554610 : ℝ) ≤
        2 * cdf (gaussianReal 0 1) (-2.1974) ∧
      2 * cdf (gaussianReal 0 1) (-2.1820) ≤ 0.029563591 := by
  have hlo := normal_tail_fine 5 2.1974 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have hhi := normal_tail_fine 5 2.1820 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial] at hlo hhi
  exact ⟨by linarith [hlo.1], by linarith [hhi.2]⟩

end SAP.P041.WH.W1.P.T8_L3

open SAP.P041.WH.W1.P.T8_L3
open AronowAudit.P041
open AronowAudit.P041.Wave1
open ProbabilityTheory

theorem SAP.P041.WH.W1.T8_L3_proof : SAP.P041.WH.W1.T8_L3 := by
  intro h s hh hs
  obtain ⟨hpos, hlt, spos, hzlo, hzhi⟩ := wald_bounds h s hh hs
  have hp := normal_endpoint_bounds
  have hpLo := normal_tail_antitone hzhi
  have hpHi := normal_tail_antitone hzlo
  refine ⟨hpos, hlt, spos, hzlo, hzhi, ?_, ?_⟩
  · unfold normalTwoSided
    exact le_trans hp.1 (by simpa using hpLo)
  · unfold normalTwoSided
    exact le_trans hpHi hp.2

