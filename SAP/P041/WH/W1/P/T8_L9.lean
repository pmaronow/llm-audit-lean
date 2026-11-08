import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P041.WH.W1.P.T8_L9

open AronowAudit.P041.Wave1
open ProbabilityTheory

private theorem lower_endpoint_tail :
    (0.01 : ℝ) < normalTwoSided 2.5758292 := by
  have hp : 0 ≤ normal_intPoly 29 2.5758292 := by
    norm_num [normal_intPoly]
  have hcert := SAP.P041.WH.W1.normal_tail_fine 14 2.5758292 (by norm_num) hp
  have hbound : (0.01 : ℝ) <
      1 - 2*0.39894228040143269*normal_intPoly 28 2.5758292 := by
    norm_num [normal_intPoly]
  have h := lt_of_lt_of_le hbound hcert.1
  unfold normalTwoSided
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.5758292)]
  exact h

private theorem upper_endpoint_tail :
    normalTwoSided 2.5758294 < (0.01 : ℝ) := by
  have hp : 0 ≤ normal_intPoly 29 2.5758294 := by
    norm_num [normal_intPoly]
  have hcert := SAP.P041.WH.W1.normal_tail_fine 14 2.5758294 (by norm_num) hp
  have hbound :
      1 - 2*0.39894228040143267*normal_intPoly 29 2.5758294 < (0.01 : ℝ) := by
    norm_num [normal_intPoly]
  have h := lt_of_le_of_lt hcert.2 hbound
  unfold normalTwoSided
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.5758294)]
  exact h


end SAP.P041.WH.W1.P.T8_L9

theorem SAP.P041.WH.W1.T8_L9_proof : SAP.P041.WH.W1.T8_L9 := by
  let c := AronowAudit.P053.normalCritical (0.01 : ℝ)
  have hc : NormalCriticalW1 0.01 c := by
    dsimp [c]
    exact SAP.P041.WH.W1.normal_critical_exists 0.01 (by norm_num) (by norm_num)
  have hmono := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
  have hlo : (2.5758292 : ℝ) < c := by
    have hEq := hc.2.1
    have hTail := SAP.P041.WH.W1.P.T8_L9.lower_endpoint_tail
    unfold normalTwoSided at hEq hTail
    rw [abs_of_pos hc.1] at hEq
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.5758292)] at hTail
    have hCDF : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-c) <
        ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-2.5758292) := by linarith
    have hNeg := hmono.lt_iff_lt.mp hCDF
    linarith
  have hhi : c < (2.5758294 : ℝ) := by
    have hEq := hc.2.1
    have hTail := SAP.P041.WH.W1.P.T8_L9.upper_endpoint_tail
    unfold normalTwoSided at hEq hTail
    rw [abs_of_pos hc.1] at hEq
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.5758294)] at hTail
    have hCDF : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-2.5758294) <
        ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-c) := by linarith
    have hNeg := hmono.lt_iff_lt.mp hCDF
    linarith
  refine ⟨c, hc, ?_⟩
  rw [abs_lt]
  constructor <;> linarith

