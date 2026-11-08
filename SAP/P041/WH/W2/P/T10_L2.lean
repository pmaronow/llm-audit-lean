import SAP.P041.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P041.WH.W2.P.T10_L2

open ProbabilityTheory

private theorem hazardWald_gt_27 (r s : ℝ)
    (hr : printedInterval 1.056 r)
    (hs : printedInterval 0.020 s ∨ printedInterval 0.019 s) :
    2.7 < hazardWald r s := by
  have hrlo : 1.0555 ≤ r := by
    rcases hr with ⟨h, _⟩
    linarith
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < s := by
    rcases hs with hs | hs <;> rcases hs with ⟨h, _⟩ <;> linarith
  have hshi : s ≤ 0.0205 := by
    rcases hs with hs | hs <;> rcases hs with ⟨_, h⟩ <;> linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hr0
  have hmul := mul_le_mul_of_nonneg_left hlog hr0.le
  have hiden : r * (1 - 1 / r) = r - 1 := by
    field_simp [ne_of_gt hr0]
  have hiden' : r * (1 - r⁻¹) = r - 1 := by
    simpa [one_div] using hiden
  have hnum : r - 1 ≤ r * Real.log r := by
    linarith [hmul, hiden']
  have hprod : 2.7 * s < r * Real.log r := by
    nlinarith
  have hdiv : 2.7 < (r * Real.log r) / s := (lt_div_iff₀ hs0).2 hprod
  simpa [hazardWald] using hdiv

private theorem normal_tail_at_27 :
    2 * cdf (gaussianReal 0 1) (-2.7) < 0.01 := by
  have hb := AronowAudit.P041.Wave1.normal_tail_bound 8 2.7 (by norm_num)
    (by norm_num [AronowAudit.P041.Wave1.normal_intPoly,
      Finset.sum_range_succ, Nat.factorial])
  have hu : 1 - 2 * 0.39894 *
      AronowAudit.P041.Wave1.normal_intPoly 17 2.7 < 0.01 := by
    norm_num [AronowAudit.P041.Wave1.normal_intPoly,
      Finset.sum_range_succ, Nat.factorial]
  exact lt_of_le_of_lt hb.2 hu

end SAP.P041.WH.W2.P.T10_L2

theorem SAP.P041.WH.W2.T10_L2_proof : SAP.P041.WH.W2.T10_L2 := by
  intro r s hr hs
  have hz : 2.7 < hazardWald r s :=
    SAP.P041.WH.W2.P.T10_L2.hazardWald_gt_27 r s hr hs
  have htail := AronowAudit.P041.Wave1.normal_tail_antitone (le_of_lt hz)
  have habs : |hazardWald r s| = hazardWald r s := abs_of_pos (by linarith)
  rw [normalTwoSided, habs]
  exact lt_of_le_of_lt htail SAP.P041.WH.W2.P.T10_L2.normal_tail_at_27
