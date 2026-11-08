import SAP.P041.WH.W1.Leaves
import AronowAudit.P041.Wave1.Gap.GP041P042P045B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open ProbabilityTheory
namespace SAP.P041.WH.W1.P.T7_L8

open ProbabilityTheory
open AronowAudit.P041.Wave1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma normal_tail_endpoints :
    0.615 < SAP.P041.normalTwoSided (64/129) ∧
    SAP.P041.normalTwoSided (64/129) < 0.625 ∧
    0.10 < SAP.P041.normalTwoSided 1 ∧
    0.01 < SAP.P041.normalTwoSided 2.5755 ∧
    SAP.P041.normalTwoSided 2.5765 < 0.01 := by
  have hA := normal_tail_bound 3 (64/129) (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have hB := normal_tail_bound 3 1 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have hC := SAP.P041.WH.W1.normal_tail_fine 8 2.5755 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  have hD := SAP.P041.WH.W1.normal_tail_fine 8 2.5765 (by norm_num)
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
  norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial] at hA hB hC hD
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [SAP.P041.normalTwoSided, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 64/129)] using
      (show 0.615 < 2 * cdf (gaussianReal 0 1) (-(64/129)) by linarith [hA.1])
  · simpa [SAP.P041.normalTwoSided, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 64/129)] using
      (show 2 * cdf (gaussianReal 0 1) (-(64/129)) < 0.625 by linarith [hA.2])
  · simpa [SAP.P041.normalTwoSided, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ))] using
      (show 0.10 < 2 * cdf (gaussianReal 0 1) (-1) by linarith [hB.1])
  · simpa [SAP.P041.normalTwoSided, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2.5755:ℝ))] using
      (show 0.01 < 2 * cdf (gaussianReal 0 1) (-2.5755) by linarith [hC.1])
  · simpa [SAP.P041.normalTwoSided, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2.5765:ℝ))] using
      (show 2 * cdf (gaussianReal 0 1) (-2.5765) < 0.01 by linarith [hD.2])

end SAP.P041.WH.W1.P.T7_L8

theorem SAP.P041.WH.W1.T7_L8_proof : SAP.P041.WH.W1.T7_L8 := by
  change SAP.P041.CitationNormalFactsW1
  obtain ⟨hA, hB, hAtOne, hLo, hHi⟩ :=
    SAP.P041.WH.W1.P.T7_L8.normal_tail_endpoints
  refine ⟨hA, hB, ?_, ?_⟩
  · intro x hx
    have hmono := AronowAudit.P041.Wave1.normal_tail_antitone
      (a := |x|) (b := 1) (le_of_lt hx)
    have hpx : SAP.P041.normalTwoSided x =
        2 * cdf (gaussianReal 0 1) (-|x|) := rfl
    have hAtOne' : 0.10 < 2 * cdf (gaussianReal 0 1) (-1) := by
      simpa [SAP.P041.normalTwoSided] using hAtOne
    rw [hpx]
    linarith
  · let c : ℝ := AronowAudit.P053.normalCritical 0.01
    have hc : SAP.P041.NormalCriticalW1 0.01 c := by
      simpa [c] using SAP.P041.WH.W1.normal_critical_exists 0.01 (by norm_num) (by norm_num)
    have hcpos : 0 < c := hc.1
    have hceq : SAP.P041.normalTwoSided c = 0.01 := hc.2.1
    have hclo : 2.5755 < c := by
      by_contra hn
      have hle : c ≤ 2.5755 := le_of_not_gt hn
      have hm := AronowAudit.P041.Wave1.normal_tail_antitone (a := c) (b := 2.5755) hle
      have hp : SAP.P041.normalTwoSided 2.5755 ≤ SAP.P041.normalTwoSided c := by
        simpa [SAP.P041.normalTwoSided, abs_of_pos hcpos,
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2.5755:ℝ))] using hm
      linarith
    have hchi : c < 2.5765 := by
      by_contra hn
      have hle : 2.5765 ≤ c := le_of_not_gt hn
      have hm := AronowAudit.P041.Wave1.normal_tail_antitone (a := 2.5765) (b := c) hle
      have hp : SAP.P041.normalTwoSided c ≤ SAP.P041.normalTwoSided 2.5765 := by
        simpa [SAP.P041.normalTwoSided, abs_of_pos hcpos,
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2.5765:ℝ))] using hm
      linarith
    exact ⟨c, hc, hclo, hchi⟩
