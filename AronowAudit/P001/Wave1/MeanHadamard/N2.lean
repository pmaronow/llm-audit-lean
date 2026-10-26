import AronowAudit.P001.Wave1.MeanHadamardBlueprint

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.MeanHadamard

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

theorem n2_proof : N2 := by
  have hp0 : IsProbabilityMeasure baseLaw := by
    constructor
    norm_num [baseLaw, Measure.add_apply, Measure.smul_apply, ENNReal.inv_two_add_inv_two]
  letI : IsProbabilityMeasure baseLaw := hp0
  have hs0 : ∀ᵐ x ∂baseLaw, x = 0 ∨ x = 2 := by
    unfold baseLaw
    apply ae_add_measure_iff.mpr
    constructor
    · exact Measure.ae_smul_measure (by simp) _
    · exact Measure.ae_smul_measure (by simp) _
  have hlp0 : MemLp id 2 baseLaw := by
    apply MemLp.of_bound measurable_id.aestronglyMeasurable 2
    filter_upwards [hs0] with x hx
    rcases hx with rfl | rfl <;> norm_num
  have hiDirac (z : ℝ) : Integrable (id : ℝ → ℝ) (Measure.dirac z) :=
    integrable_dirac (by simp)
  have hi0 : Integrable (id : ℝ → ℝ)
      ((1/2 : ℝ≥0∞) • Measure.dirac (0 : ℝ)) :=
    (hiDirac 0).smul_measure (by norm_num)
  have hi2 : Integrable (id : ℝ → ℝ)
      ((1/2 : ℝ≥0∞) • Measure.dirac (2 : ℝ)) :=
    (hiDirac 2).smul_measure (by norm_num)
  have hm0 : mean baseLaw id = 1 := by
    unfold mean baseLaw
    rw [integral_add_measure hi0 hi2]
    norm_num [integral_smul_measure, integral_dirac, smul_eq_mul]
  refine ⟨hp0, hlp0, hm0, ?_⟩
  intro n
  have hr : 0 < contR n := contR_pos n
  have hr1 : 1 ≤ contR n := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [contR]
    linarith
  have ha0 : 0 ≤ contA n := by unfold contA; positivity
  have ha1 : contA n ≤ 1 := by
    have hi : (contR n)⁻¹ ≤ 1 := (inv_le_one₀ hr).2 hr1
    have hi0 : 0 ≤ (contR n)⁻¹ := by positivity
    exact pow_le_one₀ hi0 hi
  have hcoef : 0 ≤ 1 - contA n := sub_nonneg.mpr ha1
  have hmass : ENNReal.ofReal (1-contA n) + ENNReal.ofReal (contA n) = 1 := by
    rw [← ENNReal.ofReal_add hcoef ha0]
    simp
  have hpn : IsProbabilityMeasure (contam n) := by
    constructor
    simpa [contam, Measure.add_apply, Measure.smul_apply] using hmass
  letI : IsProbabilityMeasure (contam n) := hpn
  have hsn : ∀ᵐ x ∂contam n, x = 0 ∨ x = 2 ∨ x = contR n + 1 := by
    unfold contam
    apply ae_add_measure_iff.mpr
    constructor
    · refine Measure.ae_smul_measure ?_ _
      filter_upwards [hs0] with x hx
      exact hx.elim Or.inl (fun h => Or.inr (Or.inl h))
    · exact Measure.ae_smul_measure (by simp) _
  have hlpn : MemLp id 2 (contam n) := by
    apply MemLp.of_bound measurable_id.aestronglyMeasurable (contR n + 1)
    filter_upwards [hsn] with x hx
    rcases hx with rfl | rfl | rfl
    · simpa using (by linarith : 0 ≤ contR n + 1)
    · norm_num <;> linarith
    · simp [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < contR n + 1)]
  have hiBase : Integrable (id : ℝ → ℝ) baseLaw := hlp0.integrable (by norm_num)
  have hiLeft : Integrable (id : ℝ → ℝ) (ENNReal.ofReal (1-contA n) • baseLaw) :=
    hiBase.smul_measure ENNReal.ofReal_ne_top
  have hiRight : Integrable (id : ℝ → ℝ)
      (ENNReal.ofReal (contA n) • Measure.dirac (contR n+1)) :=
    (hiDirac _).smul_measure ENNReal.ofReal_ne_top
  refine ⟨hpn, hlpn, ?_⟩
  change (∫ x, id x ∂contam n) = 1 + contT n
  unfold contam
  rw [integral_add_measure hiLeft hiRight, integral_smul_measure,
    integral_smul_measure, ENNReal.toReal_ofReal hcoef, ENNReal.toReal_ofReal ha0,
    integral_dirac]
  change (1-contA n) * mean baseLaw id + contA n * (contR n+1) = 1+contT n
  rw [hm0]
  unfold contA contT
  field_simp [hr.ne']
  <;> ring

end

end AronowAudit.P001.Wave1.MeanHadamard
