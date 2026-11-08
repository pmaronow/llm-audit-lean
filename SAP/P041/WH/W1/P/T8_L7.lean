import SAP.P041.WH.W1.Leaves
import AronowAudit.P041.P041_Wald

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W1.P.T8_L7

open AronowAudit.P041
open AronowAudit.P041.Wave1
open ProbabilityTheory

lemma centre_log_bounds :
    (1.29462717259406 : ℝ) ≤ -Real.log (0.274 : ℝ) ∧
      -Real.log (0.274 : ℝ) ≤ 1.29462717259407 := by
  have hc := neg_log_certificate (0.274 : ℝ) (by norm_num) (by norm_num) 32
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

lemma centre_abs_wald_bounds :
    (43793561147/20000000000 : ℝ) ≤
        |SAP.P041.hazardWald 0.274 0.162| ∧
      |SAP.P041.hazardWald 0.274 0.162| ≤
        2189678057351/1000000000000 := by
  have h0 : (0 : ℝ) < 0.274 := by norm_num
  have h1 : (0.274 : ℝ) < 1 := by norm_num
  have hs : (0 : ℝ) < 0.162 := by norm_num
  have habs := AronowAudit.P041.abs_hazard_wald 0.274 0.162 h0 h1 hs
  have habs' : |SAP.P041.hazardWald 0.274 0.162| =
      0.274*(-Real.log 0.274)/0.162 := by
    simpa [SAP.P041.hazardWald, AronowAudit.P041.hazardWald] using habs
  rw [habs']
  constructor
  · apply (le_div_iff₀ hs).2
    nlinarith [centre_log_bounds.1]
  · apply (div_le_iff₀ hs).2
    nlinarith [centre_log_bounds.2]

lemma centre_normal_tail_bounds :
    (0.02854759 : ℝ) ≤
        2*cdf (gaussianReal 0 1)
          (-|SAP.P041.hazardWald 0.274 0.162|) ∧
      2*cdf (gaussianReal 0 1)
          (-|SAP.P041.hazardWald 0.274 0.162|) ≤ 0.028547599 := by
  have hz := centre_abs_wald_bounds
  have htHi := normal_tail_fine 14 (2189678057351/1000000000000 : ℝ)
    (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have htLo := normal_tail_fine 14 (43793561147/20000000000 : ℝ)
    (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial] at htHi htLo
  have hmonoLo := normal_tail_antitone hz.2
  have hmonoHi := normal_tail_antitone hz.1
  constructor
  · linarith [htHi.1, hmonoLo]
  · linarith [htLo.2, hmonoHi]

end SAP.P041.WH.W1.P.T8_L7

open SAP.P041.WH.W1.P.T8_L7
open ProbabilityTheory

theorem SAP.P041.WH.W1.T8_L7_proof : SAP.P041.WH.W1.T8_L7 := by
  change SAP.P041.hazardWald 0.274 0.162 < 0 ∧
    |SAP.P041.hazardWald 0.274 0.162 - (-2.18967)| < 0.00001 ∧
    |SAP.P041.normalTwoSided (SAP.P041.hazardWald 0.274 0.162) - 0.0285475| <
      0.0000001
  have h0 : (0 : ℝ) < 0.274 := by norm_num
  have h1 : (0.274 : ℝ) < 1 := by norm_num
  have hs : (0 : ℝ) < 0.162 := by norm_num
  have hlogneg : Real.log (0.274 : ℝ) < 0 := Real.log_neg h0 h1
  have hzneg : SAP.P041.hazardWald 0.274 0.162 < 0 := by
    unfold SAP.P041.hazardWald
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hlogneg) hs
  have hz := centre_abs_wald_bounds
  have hzabs : |SAP.P041.hazardWald 0.274 0.162| =
      -SAP.P041.hazardWald 0.274 0.162 := abs_of_neg hzneg
  have hzEq : SAP.P041.hazardWald 0.274 0.162 =
      -|SAP.P041.hazardWald 0.274 0.162| := by linarith [hzabs]
  have hdiffneg : SAP.P041.hazardWald 0.274 0.162 + 2.18967 < 0 := by
    rw [hzEq]
    norm_num at hz
    linarith [hz.1]
  have hstat :
      |SAP.P041.hazardWald 0.274 0.162 - (-2.18967)| < 0.00001 := by
    rw [sub_neg_eq_add, abs_of_neg hdiffneg, hzEq]
    norm_num at hz
    linarith [hz.2]
  have hp := centre_normal_tail_bounds
  have hpEq : SAP.P041.normalTwoSided (SAP.P041.hazardWald 0.274 0.162) =
      2*cdf (gaussianReal 0 1)
        (-|SAP.P041.hazardWald 0.274 0.162|) := rfl
  have hpErr :
      |SAP.P041.normalTwoSided (SAP.P041.hazardWald 0.274 0.162) - 0.0285475| <
        0.0000001 := by
    rw [hpEq]
    apply abs_lt.mpr
    constructor <;> linarith [hp.1, hp.2]
  exact ⟨hzneg, hstat, hpErr⟩
