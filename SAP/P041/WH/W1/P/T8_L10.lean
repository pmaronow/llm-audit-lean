import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ProbabilityTheory

noncomputable section

namespace SAP.P041.WH.W1.P.T8_L10

open AronowAudit.P041.Wave1
open ProbabilityTheory

end SAP.P041.WH.W1.P.T8_L10

theorem SAP.P041.WH.W1.T8_L10_proof : SAP.P041.WH.W1.T8_L10 := by
  let xlo : ℝ := 1.9599639
  let xhi : ℝ := 1.9599641
  obtain ⟨hcpos, hceq, hcuniq⟩ :=
    SAP.P041.WH.W1.normal_critical_exists 0.05 (by norm_num) (by norm_num)
  have hpLo : 0 ≤ AronowAudit.P041.Wave1.normal_intPoly 29 xlo := by
    norm_num [xlo, AronowAudit.P041.Wave1.normal_intPoly,
      Finset.sum_range_succ, Nat.factorial]
  have hpHi : 0 ≤ AronowAudit.P041.Wave1.normal_intPoly 29 xhi := by
    norm_num [xhi, AronowAudit.P041.Wave1.normal_intPoly,
      Finset.sum_range_succ, Nat.factorial]
  have htailLo := SAP.P041.WH.W1.normal_tail_fine 14 xlo (by norm_num [xlo]) hpLo
  have htailHi := SAP.P041.WH.W1.normal_tail_fine 14 xhi (by norm_num [xhi]) hpHi
  have hcertLo : (0.05 : ℝ) <
      1 - 2*0.39894228040143269 * AronowAudit.P041.Wave1.normal_intPoly 28 xlo := by
    norm_num [xlo, AronowAudit.P041.Wave1.normal_intPoly,
      Finset.sum_range_succ, Nat.factorial]
  have hcertHi :
      1 - 2*0.39894228040143267 * AronowAudit.P041.Wave1.normal_intPoly 29 xhi <
        (0.05 : ℝ) := by
    norm_num [xhi, AronowAudit.P041.Wave1.normal_intPoly,
      Finset.sum_range_succ, Nat.factorial]
  have htailLo' : (0.05 : ℝ) <
      2*ProbabilityTheory.cdf (gaussianReal 0 1) (-xlo) := lt_of_lt_of_le hcertLo htailLo.1
  have htailHi' : 2*ProbabilityTheory.cdf (gaussianReal 0 1) (-xhi) < (0.05 : ℝ) :=
    lt_of_le_of_lt htailHi.2 hcertHi
  have hcTail : 2*ProbabilityTheory.cdf (gaussianReal 0 1) (-AronowAudit.P053.normalCritical 0.05) =
      (0.05 : ℝ) := by
    simpa only [SAP.P041.normalTwoSided, abs_of_pos hcpos] using hceq
  have hm := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
  have hLo : xlo < AronowAudit.P053.normalCritical 0.05 := by
    have hlt : ProbabilityTheory.cdf (gaussianReal 0 1) (-AronowAudit.P053.normalCritical 0.05) <
        ProbabilityTheory.cdf (gaussianReal 0 1) (-xlo) := by linarith
    have harg := hm.lt_iff_lt.mp hlt
    dsimp [xlo] at harg ⊢
    linarith
  have hHi : AronowAudit.P053.normalCritical 0.05 < xhi := by
    have hlt : ProbabilityTheory.cdf (gaussianReal 0 1) (-xhi) <
        ProbabilityTheory.cdf (gaussianReal 0 1) (-AronowAudit.P053.normalCritical 0.05) := by linarith
    have harg := hm.lt_iff_lt.mp hlt
    dsimp [xhi] at harg ⊢
    linarith
  have hdist : |AronowAudit.P053.normalCritical 0.05 - 1.9599640| < 0.0000001 := by
    rw [abs_lt]
    constructor <;> linarith
  exact ⟨AronowAudit.P053.normalCritical 0.05,
    ⟨hcpos, hceq, hcuniq⟩, hdist⟩
