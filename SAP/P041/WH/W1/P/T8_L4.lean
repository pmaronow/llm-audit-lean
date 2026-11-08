import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W1.P.T8_L4

open ProbabilityTheory

lemma endpoint_logs :
    (1.15359659 : ℝ) < -Real.log (631/2000:ℝ) ∧
      -Real.log (631/2000:ℝ) < 1.15359660 ∧
    (1.15043203 : ℝ) < -Real.log (633/2000:ℝ) ∧
      -Real.log (633/2000:ℝ) < 1.15043205 := by
  have hc₁ := AronowAudit.P041.neg_log_certificate (631/2000:ℝ)
    (by norm_num) (by norm_num) 32
  have hc₂ := AronowAudit.P041.neg_log_certificate (633/2000:ℝ)
    (by norm_num) (by norm_num) 32
  norm_num [AronowAudit.P041.logSeries, Finset.sum_range_succ] at hc₁ hc₂
  have h₁ : (1.15359659 : ℝ) < -Real.log (631/2000:ℝ) := by linarith [hc₁.1]
  have h₂ : -Real.log (631/2000:ℝ) < 1.15359660 := by linarith [hc₁.2]
  have h₃ : (1.15043203 : ℝ) < -Real.log (633/2000:ℝ) := by linarith [hc₂.1]
  have h₄ : -Real.log (633/2000:ℝ) < 1.15043205 := by linarith [hc₂.2]
  exact ⟨h₁,h₂,h₃,h₄⟩

lemma statistic_bounds (h s : ℝ) (hh : SAP.P041.printedInterval 0.316 h)
    (hs : SAP.P041.printedInterval 0.149 s) :
    0 < h ∧ h < 1 ∧ 0 < s ∧
      2.4345 ≤ |SAP.P041.hazardWald h s| ∧
      |SAP.P041.hazardWald h s| ≤ 2.4520 := by
  rcases hh with ⟨hlo,hhi⟩
  rcases hs with ⟨slo,shi⟩
  have h0 : 0 < h := by linarith
  have h1 : h < 1 := by linarith
  have s0 : 0 < s := by linarith
  have hlog := endpoint_logs
  have huLog : Real.log (633/2000:ℝ) ≤ -1 := by linarith [hlog.2.2.1]
  have hn := AronowAudit.P041.wald_numerator_below (631/2000:ℝ)
    (633/2000:ℝ) h (by norm_num) (by linarith) (by linarith) huLog
  have habs := AronowAudit.P041.abs_hazard_wald h s h0 h1 s0
  have habs' : |SAP.P041.hazardWald h s| = h*(-Real.log h)/s := by
    simpa [SAP.P041.hazardWald, AronowAudit.P041.hazardWald] using habs
  rw [habs']
  refine ⟨h0,h1,s0,?_,?_⟩
  · apply (le_div_iff₀ s0).2
    nlinarith [hn.1, hlog.1]
  · apply (div_le_iff₀ s0).2
    nlinarith [hn.2, hlog.2.2.2]

end SAP.P041.WH.W1.P.T8_L4

theorem SAP.P041.WH.W1.T8_L4_proof : SAP.P041.WH.W1.T8_L4 := by
  intro h s hh hs
  have hz := SAP.P041.WH.W1.P.T8_L4.statistic_bounds h s hh hs
  obtain ⟨h0,h1,s0,hlo,hhi⟩ := hz
  have htHi := SAP.P041.WH.W1.normal_tail_fine 14 2.452 (by norm_num)
    (by norm_num [AronowAudit.P041.Wave1.normal_intPoly,
      Finset.sum_range_succ, Nat.factorial])
  have htLo := SAP.P041.WH.W1.normal_tail_fine 14 2.4345 (by norm_num)
    (by norm_num [AronowAudit.P041.Wave1.normal_intPoly,
      Finset.sum_range_succ, Nat.factorial])
  norm_num [AronowAudit.P041.Wave1.normal_intPoly, Finset.sum_range_succ,
    Nat.factorial] at htHi htLo
  have hpLo := AronowAudit.P041.Wave1.normal_tail_antitone hhi
  have hpHi := AronowAudit.P041.Wave1.normal_tail_antitone hlo
  have hpLower : 0.013945057 ≤
      2*ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
        (-|SAP.P041.hazardWald h s|) := by
    linarith [htHi.1]
  have hpUpper :
      2*ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
        (-|SAP.P041.hazardWald h s|) ≤ 0.015189259 := by
    linarith [htLo.2]
  have hpEq : SAP.P041.normalTwoSided (SAP.P041.hazardWald h s) =
      2*ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
        (-|SAP.P041.hazardWald h s|) := rfl
  refine ⟨h0,h1,s0,hlo,hhi,?_,?_⟩
  · rw [hpEq]
    exact hpLower
  · rw [hpEq]
    exact hpUpper
