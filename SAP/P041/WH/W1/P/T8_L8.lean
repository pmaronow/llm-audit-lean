import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open AronowAudit.P041.Wave1
open ProbabilityTheory

theorem SAP.P041.WH.W1.T8_L8_proof : SAP.P041.WH.W1.T8_L8 := by
  change AronowAudit.P041.hazardWald 0.316 0.149 < 0 ∧
    |AronowAudit.P041.hazardWald 0.316 0.149 - (-2.44319)| < 0.00001 ∧
    |AronowAudit.P041.normalTwoSided (AronowAudit.P041.hazardWald 0.316 0.149) -
      0.0145578| < 0.0000001
  have hlog := AronowAudit.P041.neg_log_certificate 0.316 (by norm_num) (by norm_num) 30
  norm_num [AronowAudit.P041.logSeries, Finset.sum_range_succ] at hlog
  have habs := AronowAudit.P041.abs_hazard_wald 0.316 0.149
    (by norm_num) (by norm_num) (by norm_num)
  have hz : (2.443195494394 : ℝ) ≤
      |AronowAudit.P041.hazardWald 0.316 0.149| ∧
      |AronowAudit.P041.hazardWald 0.316 0.149| ≤ (2.443195494396 : ℝ) := by
    rw [habs]
    constructor
    · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 0.149)).2
      nlinarith [hlog.1]
    · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 0.149)).2
      nlinarith [hlog.2]
  have hnneg : AronowAudit.P041.hazardWald 0.316 0.149 < 0 := by
    unfold AronowAudit.P041.hazardWald
    apply div_neg_of_neg_of_pos
    · exact mul_neg_of_pos_of_neg (by norm_num)
        (Real.log_neg (by norm_num) (by norm_num))
    · norm_num
  have hstat : |AronowAudit.P041.hazardWald 0.316 0.149 - (-2.44319)| < 0.00001 := by
    rw [abs_lt]
    rw [abs_of_neg hnneg] at hz
    constructor <;> linarith
  have htailLo := normal_tail_fine 14 2.443195494396 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have htailHi := normal_tail_fine 14 2.443195494394 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial] at htailLo htailHi
  have hp : (0.01455784 : ℝ) ≤
      AronowAudit.P041.normalTwoSided (AronowAudit.P041.hazardWald 0.316 0.149) ∧
      AronowAudit.P041.normalTwoSided (AronowAudit.P041.hazardWald 0.316 0.149) ≤ 0.01455786 := by
    unfold AronowAudit.P041.normalTwoSided
    constructor
    · have hm := normal_tail_antitone hz.2
      linarith [htailLo.1]
    · have hm := normal_tail_antitone hz.1
      linarith [htailHi.2]
  refine ⟨?_, hstat, ?_⟩
  · exact hnneg
  · rw [abs_lt]
    constructor <;> linarith [hp.1, hp.2]

