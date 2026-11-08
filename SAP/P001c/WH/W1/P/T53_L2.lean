import SAP.P001c.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace SAP.P001c.WH.W1.P.T53_L2

noncomputable section

def p : unitInterval := ⟨7 / 8, by norm_num, by norm_num⟩

lemma hp : p ≠ 0 := by
  intro h
  have hh : (p : ℝ) = 0 := congrArg Subtype.val h
  norm_num [p] at hh

lemma weight_eq (k : ℕ) :
    (1 - (p : ℝ)) ^ k * (p : ℝ) = (7 / 8 : ℝ) * (1 / 8 : ℝ) ^ k := by
  norm_num [p]
  ring

lemma moment_weight_eq (k : ℕ) :
    ((1 - (p : ℝ)) ^ k * (p : ℝ)) *
        ((SAP.P001c.powerTailValue k) ^ 4) =
      (2 : ℝ) ^ (4 * k) * AronowAudit.P001.heavyMomentMass k := by
  have hpow : (2 : ℝ) ^ (4 * k) = ((2 : ℝ) ^ k) ^ 4 := by
    rw [show 4 * k = k * 4 by omega, pow_mul]
  have hmass : AronowAudit.P001.heavyMomentMass k =
      (7 / 8 : ℝ) * (1 / 8 : ℝ) ^ k := by
    simp [AronowAudit.P001.heavyMomentMass, pow_succ]
    ring
  rw [weight_eq k, SAP.P001c.powerTailValue, hpow, hmass]
  ring

lemma moment_weight_norm_eq (k : ℕ) :
    ((1 - (p : ℝ)) ^ k * (p : ℝ)) *
      ‖(SAP.P001c.powerTailValue k) ^ 4‖ =
      (2 : ℝ) ^ (4 * k) * AronowAudit.P001.heavyMomentMass k := by
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact moment_weight_eq k

lemma law_eq : SAP.P001c.powerTailLaw = geometricMeasure p := by
  rfl

lemma lintegral_fourth_eq_series :
    (∫⁻ k, ENNReal.ofReal ((SAP.P001c.powerTailValue k) ^ 4)
      ∂SAP.P001c.powerTailLaw) =
      ∑' k : ℕ,
        ENNReal.ofReal ((1 - (p : ℝ)) ^ k * (p : ℝ)) *
          ENNReal.ofReal ((SAP.P001c.powerTailValue k) ^ 4) := by
  rw [law_eq, ProbabilityTheory.geometricMeasure_eq hp,
    MeasureTheory.lintegral_sum_measure]
  apply tsum_congr
  intro k
  rw [MeasureTheory.lintegral_smul_measure,
    MeasureTheory.lintegral_dirac' k (measurable_of_countable _)]
  simp

lemma fourth_integral_eq_infty :
    (∫⁻ k, ENNReal.ofReal ((SAP.P001c.powerTailValue k) ^ 4)
      ∂SAP.P001c.powerTailLaw) = ∞ := by
  obtain ⟨_, _, _, _, _, _, hdiv, _⟩ :=
    AronowAudit.P001.squares_missing_wlln_hypothesis
  calc
    (∫⁻ k, ENNReal.ofReal ((SAP.P001c.powerTailValue k) ^ 4)
        ∂SAP.P001c.powerTailLaw) =
        ∑' k : ℕ,
          ENNReal.ofReal ((1 - (p : ℝ)) ^ k * (p : ℝ)) *
            ENNReal.ofReal ((SAP.P001c.powerTailValue k) ^ 4) :=
      lintegral_fourth_eq_series
    _ = ∑' k : ℕ,
          ENNReal.ofReal ((2 : ℝ) ^ (4 * k) * AronowAudit.P001.heavyMomentMass k) := by
      congr 1
      funext k
      have hw : 0 ≤ (1 - (p : ℝ)) ^ k * (p : ℝ) := by
        rw [weight_eq k]
        positivity
      rw [← ENNReal.ofReal_mul hw]
      exact congrArg ENNReal.ofReal (moment_weight_eq k)
    _ = ∞ := hdiv

end
end SAP.P001c.WH.W1.P.T53_L2

theorem SAP.P001c.WH.W1.T53_L2_proof : SAP.P001c.WH.W1.T53_L2 := by
  have hdiv := SAP.P001c.WH.W1.P.T53_L2.fourth_integral_eq_infty
  have hnot : ¬ MemLp (fun k => (SAP.P001c.powerTailValue k) ^ 2) 2
      SAP.P001c.powerTailLaw := by
    intro hmem
    have hintSq : Integrable
        (fun k => ((SAP.P001c.powerTailValue k) ^ 2) ^ 2)
        SAP.P001c.powerTailLaw := hmem.integrable_sq
    have hint : Integrable (fun k => (SAP.P001c.powerTailValue k) ^ 4)
        SAP.P001c.powerTailLaw := by
      convert hintSq using 1
      ext k
      ring
    change Integrable (fun k => (SAP.P001c.powerTailValue k) ^ 4)
      (geometricMeasure SAP.P001c.WH.W1.P.T53_L2.p) at hint
    have hs := (ProbabilityTheory.integrable_geometricMeasure_iff SAP.P001c.WH.W1.P.T53_L2.hp).mp hint
    have hreal : Summable
        (fun k => (2 : ℝ) ^ (4 * k) * AronowAudit.P001.heavyMomentMass k) := by
      apply hs.congr
      intro k
      exact SAP.P001c.WH.W1.P.T53_L2.moment_weight_norm_eq k
    have hfinite := hreal.tsum_ofReal_lt_top
    have hseries :=
      AronowAudit.P001.squares_missing_wlln_hypothesis
    obtain ⟨_, _, _, _, _, _, hdivSeries, _⟩ := hseries
    rw [hdivSeries] at hfinite
    exact (lt_irrefl (∞ : ℝ≥0∞)) hfinite
  have hmeas : Measurable
      (fun k => (SAP.P001c.powerTailValue k) ^ 2) := by
    exact measurable_of_countable _
  have hvar : evariance
      (fun k => (SAP.P001c.powerTailValue k) ^ 2)
      SAP.P001c.powerTailLaw = ∞ := by
    letI : IsProbabilityMeasure SAP.P001c.powerTailLaw := by
      unfold SAP.P001c.powerTailLaw
      infer_instance
    exact evariance_eq_top hmeas.aestronglyMeasurable hnot
  exact ⟨hdiv, hnot, hvar⟩


