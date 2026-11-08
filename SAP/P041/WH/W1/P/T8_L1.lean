import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W1.P.T8_L1

private theorem log_lower_endpoint :
    (0.4012241 : ℝ) < -Real.log (0.6695) ∧
      -Real.log (0.6695) < 0.4012242 := by
  have hc := AronowAudit.P041.neg_log_certificate 0.6695 (by norm_num) (by norm_num) 32
  norm_num [AronowAudit.P041.logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

private theorem log_upper_endpoint :
    (0.3997315 : ℝ) < -Real.log (0.6705) ∧
      -Real.log (0.6705) < 0.3997317 := by
  have hc := AronowAudit.P041.neg_log_certificate 0.6705 (by norm_num) (by norm_num) 32
  norm_num [AronowAudit.P041.logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

private theorem normal_endpoints :
    0.004416378 ≤ 2 * ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal 0 1) (-2.8426) ∧
      2 * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-2.8064) ≤
        0.005073862 := by
  have hu := SAP.P041.WH.W1.normal_tail_fine 14 2.8426 (by norm_num)
    (by norm_num [AronowAudit.P041.Wave1.normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have hl := SAP.P041.WH.W1.normal_tail_fine 14 2.8064 (by norm_num)
    (by norm_num [AronowAudit.P041.Wave1.normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  norm_num [AronowAudit.P041.Wave1.normal_intPoly, Finset.sum_range_succ, Nat.factorial] at hu hl
  constructor <;> linarith

end SAP.P041.WH.W1.P.T8_L1

theorem SAP.P041.WH.W1.T8_L1_proof : SAP.P041.WH.W1.T8_L1 := by
  intro h s hh hs
  have hbounds : (0.6695 : ℝ) ≤ h ∧ h ≤ 0.6705 := by
    norm_num [SAP.P041.printedInterval] at hh ⊢
    exact hh
  have sbounds : (0.0945 : ℝ) ≤ s ∧ s ≤ 0.0955 := by
    norm_num [SAP.P041.printedInterval] at hs ⊢
    exact hs
  have hp : 0 < h := by linarith
  have hlt : h < 1 := by linarith
  have hspos : 0 < s := by linarith
  have hlog : -1 ≤ Real.log (0.6695 : ℝ) := by
    have := SAP.P041.WH.W1.P.T8_L1.log_lower_endpoint.2
    linarith
  have hnum := AronowAudit.P041.wald_numerator_above 0.6695 0.6705 h
    (by norm_num) hbounds.1 hbounds.2 hlog
  have hnumlo : (0.2680199 : ℝ) < 0.6705 * (-Real.log 0.6705) := by
    have := mul_lt_mul_of_pos_left
      SAP.P041.WH.W1.P.T8_L1.log_upper_endpoint.1 (by norm_num : (0 : ℝ) < 0.6705)
    norm_num at this ⊢
    linarith
  have hnumhi : 0.6695 * (-Real.log 0.6695) < (0.2686197 : ℝ) := by
    have := mul_lt_mul_of_pos_left
      SAP.P041.WH.W1.P.T8_L1.log_lower_endpoint.2 (by norm_num : (0 : ℝ) < 0.6695)
    norm_num at this ⊢
    linarith
  have habs := AronowAudit.P041.abs_hazard_wald h s hp hlt hspos
  have hz : (2.8064 : ℝ) ≤ |AronowAudit.P041.hazardWald h s| ∧
      |AronowAudit.P041.hazardWald h s| ≤ 2.8426 := by
    rw [habs]
    constructor
    · apply (le_div_iff₀ hspos).2
      nlinarith [hnum.1, sbounds.2]
    · apply (div_le_iff₀ hspos).2
      nlinarith [hnum.2, sbounds.1]
  have htail := SAP.P041.WH.W1.P.T8_L1.normal_endpoints
  have hpRange : (0.004416378 : ℝ) ≤
      AronowAudit.P041.normalTwoSided (AronowAudit.P041.hazardWald h s) ∧
      AronowAudit.P041.normalTwoSided (AronowAudit.P041.hazardWald h s) ≤ 0.005073862 := by
    rw [AronowAudit.P041.normalTwoSided]
    constructor
    · have hm := AronowAudit.P041.Wave1.normal_tail_antitone hz.2
      have he : |AronowAudit.P041.hazardWald h s| ≤ 2.8426 := hz.2
      have hm' := AronowAudit.P041.Wave1.normal_tail_antitone he
      linarith [htail.1]
    · have hm := AronowAudit.P041.Wave1.normal_tail_antitone hz.1
      have he : 2.8064 ≤ |AronowAudit.P041.hazardWald h s| := hz.1
      have hm' := AronowAudit.P041.Wave1.normal_tail_antitone he
      linarith [htail.2]
  refine ⟨hp, hlt, hspos, hz.1, hz.2, hpRange.1, hpRange.2⟩
