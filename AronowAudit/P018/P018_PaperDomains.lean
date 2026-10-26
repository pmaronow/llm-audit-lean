import Mathlib.Tactic

namespace AronowAudit.P018.PaperDomains

/-- Universal significance-ratio implications for T24(iv), without positivity of se. -/
def PrintedSignificanceRounding : Prop := ∀ b se : ℝ,
    (|b| ≤ 23/2000 → 15/2000 ≤ se → |b|/se ≤ 23/15 ∧ (23/15 : ℝ) < 41/25) ∧
    (21/2000 ≤ |b| → se ≤ 5/2000 →
      21/5 ≤ |b|/se ∧ (41/25 : ℝ) < 21/5)

/-- The significance-ratio implication without denominator positivity is false.
The table's standard errors are positive. -/
theorem printed_significance_rounding_refuted : ¬ PrintedSignificanceRounding := by
  intro h
  have hh := (h (21/2000) 0).2 (by norm_num) (by norm_num)
  norm_num at hh

/-- Every real coefficient and pair of SEs in the conservative rounding
intervals of the displayed international-organizations row gives the claimed
opposite significance decisions. Positivity follows from the actual interval. -/
theorem significance_on_rounding_intervals (b dyadic hc : ℝ)
    (hb : 21/2000 ≤ |b| ∧ |b| ≤ 23/2000)
    (hdyadic : 15/2000 ≤ dyadic ∧ dyadic ≤ 17/2000)
    (hhc : 3/2000 ≤ hc ∧ hc ≤ 5/2000) :
    |b| / dyadic ≤ 23/15 ∧ (23/15 : ℝ) < 41/25 ∧
      21/5 ≤ |b| / hc ∧ (41/25 : ℝ) < 21/5 := by
  have hd : 0 < dyadic := by linarith [hdyadic.1]
  have hh : 0 < hc := by linarith [hhc.1]
  refine ⟨(div_le_iff₀ hd).mpr ?_, by norm_num,
    (le_div_iff₀ hh).mpr ?_, by norm_num⟩
  · linarith [hb.2,hdyadic.1]
  · linarith [hb.1,hhc.2]

end AronowAudit.P018.PaperDomains
