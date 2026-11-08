import SAP.P041.WH.W1.Helpers

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W1
open scoped BigOperators
open AronowAudit.P041.Wave1

theorem active_rejection (h s : ℝ) (hh : printedInterval 0.629 h)
    (hs : printedInterval 0.091 s) : normalTwoSided (hazardWald h s) < 0.01 := by
  have hz : 3.17 < |hazardWald h s| ∧ |hazardWald h s| < 3.24 :=
    AronowAudit.P041.wald_active_rounding h s hh hs
  have ht := normal_tail_antitone (show (2.80 : ℝ) ≤ |hazardWald h s| by linarith [hz.1])
  exact lt_of_le_of_lt ht normal_star_endpoints.1

set_option maxRecDepth 10000 in
theorem living_rounding_witness :
    ∃ h s : ℝ, 0.7745 < h ∧ h < 0.7755 ∧ 0.5025 < s ∧ s < 0.5035 ∧
      0.695 ≤ normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.705 := by
  have hl := AronowAudit.P041.neg_log_certificate 0.7754 (by norm_num) (by norm_num) 10
  norm_num [AronowAudit.P041.logSeries, Finset.sum_range_succ] at hl
  have hz : |hazardWald 0.7754 0.5034| ≤ 0.3919 := by
    have habs : |hazardWald 0.7754 0.5034| = 0.7754 * (-Real.log 0.7754) / 0.5034 :=
      AronowAudit.P041.abs_hazard_wald 0.7754 0.5034 (by norm_num) (by norm_num) (by norm_num)
    rw [habs]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 0.5034)).mpr
    linarith [hl.2]
  have ht := normal_tail_bound 4 0.3919 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial] at ht
  have hm := normal_tail_antitone hz
  have hu := t11_existing.1.2.1 0.7754 0.5034
    (by norm_num [printedInterval]) (by norm_num [printedInterval])
  refine ⟨0.7754,0.5034,by norm_num,by norm_num,by norm_num,by norm_num,?_,?_⟩
  · change 0.695 ≤ 2 * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
      (-|hazardWald 0.7754 0.5034|)
    linarith [ht.1]
  · linarith [hu.2]

theorem t11_complete : T11WholeStatement := by
  have hp := Bridge.proportional_hazards (4/5) (by norm_num) (by norm_num)
  have hf := Bridge.proportional_hazards (99/100) (by norm_num) (by norm_num)
  obtain ⟨hpA,hnA,dA,hpF,hnF,dF,_,_,_,_,hrA,hrF,hne,
    remAN,remAP,remFN,remFP,_,_,_,_,_,_,_,_,probAN,probAP,probFN,probFP⟩ :=
    Bridge.common_bias_countermodel
  have hlik : 0 < ModelCountLikelihoodW1 (4/5) (99/100) := by
    unfold ModelCountLikelihoodW1
    rw [remAN,remAP,remFN,remFP]
    exact mul_pos (mul_pos (mul_pos probAN probAP) probFN) probFP
  have hcontrast : |observedSurvivalContrast 75 76 3 1| <
      |observedSurvivalContrast 150 150 52 75| := by norm_num [observedSurvivalContrast]
  have hcontrast7 : |observedSurvivalContrast 75 76 7 3| <
      |observedSurvivalContrast 150 150 82 101| := by norm_num [observedSurvivalContrast]
  have hdf : 0 < twelveHourContrast (99/100) := by rw [dF]; norm_num
  have hd13 : 13 * twelveHourContrast (99/100) < twelveHourContrast (4/5) := by
    rw [dF,dA]; norm_num
  have hd : twelveHourContrast (99/100) < twelveHourContrast (4/5) := by
    rw [dF,dA]; norm_num
  have hrej := active_rejection 0.629 0.091
    (by norm_num [printedInterval]) (by norm_num [printedInterval])
  have hnon : 0.10 < normalTwoSided (hazardWald 0.691 0.318) := by
    have hh := t11_existing.1.1 0.691 0.318
      (by norm_num [printedInterval]) (by norm_num [printedInterval])
    linarith [hh.1]
  have href : ¬ SuppliedEvidenceImpliesNullW1 := by
    intro h
    have he := h (4/5) (99/100) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hrej hnon hcontrast hdf hd hlik
    rw [hrF] at he
    norm_num at he
  refine ⟨href,t11_existing,t2_existing,active_rejection,?_,?_,living_rounding_witness,
    hcontrast,hcontrast7,hp.1,hp.2.1,hf.1,hf.2.1,hrA,hrF,hne,dA,dF,hdf,hd13,
    remAN,remAP,remFN,remFP,probAN,probAP,probFN,probFP,hlik⟩
  · intro h s hh hs
    have hc := t11_existing.1.1 h s hh hs
    exact ⟨by linarith [hc.1],by linarith [hc.2]⟩
  · intro h s hh hs
    have hc := t11_existing.1.2.2.1 h s hh hs
    exact ⟨by linarith [hc.1],by linarith [hc.2]⟩

theorem t12_complete : T12WholeStatement := by
  refine ⟨t12_existing, ?_⟩
  norm_num [relativeIncrease, roundsWhole]

end SAP.P041.WH.W1
