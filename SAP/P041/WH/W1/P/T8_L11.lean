import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P041.WH.W1.P.T8_L11

open AronowAudit.P041.Wave1
open ProbabilityTheory

set_option maxRecDepth 10000 in
theorem endpoint_tails :
    0.10 < 2 * cdf (gaussianReal 0 1) (-(1.6448535 : ℝ)) ∧
    2 * cdf (gaussianReal 0 1) (-(1.6448537 : ℝ)) < 0.10 := by
  have hlowx : 0 ≤ (1.6448535 : ℝ) := by norm_num
  have huppx : 0 ≤ (1.6448537 : ℝ) := by norm_num
  have hlowp : 0 ≤ normal_intPoly 29 (1.6448535 : ℝ) := by
    norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial]
  have huppp : 0 ≤ normal_intPoly 29 (1.6448537 : ℝ) := by
    norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial]
  have hlow := SAP.P041.WH.W1.normal_tail_fine 14 1.6448535 hlowx hlowp
  have hupp := SAP.P041.WH.W1.normal_tail_fine 14 1.6448537 huppx huppp
  constructor
  · norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial] at hlow
    linarith [hlow.1]
  · norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial] at hupp
    linarith [hupp.2]

end SAP.P041.WH.W1.P.T8_L11

theorem SAP.P041.WH.W1.T8_L11_proof : SAP.P041.WH.W1.T8_L11 := by
  let a : ℝ := 1.6448535
  let b : ℝ := 1.6448537
  let c : ℝ := AronowAudit.P053.normalCritical 0.10
  have hc : SAP.P041.NormalCriticalW1 0.10 c := by
    simpa [c] using SAP.P041.WH.W1.normal_critical_exists 0.10 (by norm_num) (by norm_num)
  have hcdf : 2 * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-c) = 0.10 := by
    simpa [SAP.P041.normalTwoSided, abs_of_pos hc.1] using hc.2.1
  have htails := SAP.P041.WH.W1.P.T8_L11.endpoint_tails
  have hleft : a < c := by
    have hcmp : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-c) <
        ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a) := by
      dsimp [a]
      linarith [htails.1, hcdf]
    have hm := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
    have hord := hm.lt_iff_lt.mp hcmp
    dsimp [a] at hord ⊢
    linarith
  have hright : c < b := by
    have hcmp : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-b) <
        ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-c) := by
      dsimp [b]
      linarith [htails.2, hcdf]
    have hm := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
    have hord := hm.lt_iff_lt.mp hcmp
    dsimp [b] at hord ⊢
    linarith
  refine ⟨c, hc, ?_⟩
  apply abs_lt.mpr
  have hleft' : (1.6448535 : ℝ) < c := by simpa [a] using hleft
  have hright' : c < (1.6448537 : ℝ) := by simpa [b] using hright
  constructor <;> norm_num at hleft' hright' ⊢ <;> linarith
