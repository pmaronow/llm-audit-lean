import AronowAudit.P027.Wave1.UniformStart.N2

/-! Normalization and cell masses of the continuous uniform-start measure. -/

namespace AronowAudit.P027.Wave1.UniformStart

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory
attribute [local instance] Classical.propDecidable

theorem n4_proof : N4 := by
  intro r hr
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrR
  have hL : (0 : ℝ) < 12 * (r : ℝ) := by positivity
  have hprob : IsProbabilityMeasure (startMeasure r) := by
    apply isProbabilityMeasure_iff.mpr
    simp only [startMeasure, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply_univ, Real.volume_Ico, sub_zero]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hL)
      ENNReal.ofReal_ne_top
  refine ⟨hprob, ?_, ?_⟩
  · unfold startMeasure
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ico.compl]
    simp only [Set.compl_inter_self, measure_empty, smul_zero]
  · intro g
    have hsub : phaseInterval g ⊆ Set.Ico (0 : ℝ) (12 * (r : ℝ)) :=
      (n2_proof r).1 g
    have hmeas : MeasurableSet (phaseInterval g) := measurableSet_Ico
    have hmass : startMeasure r (phaseInterval g) =
        ENNReal.ofReal ((if g.2 = 0 then (2 : ℝ) else 10) / (12 * (r : ℝ))) := by
      unfold startMeasure
      rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hmeas,
        Set.inter_eq_left.mpr hsub]
      rw [phaseInterval, Real.volume_Ico]
      simp only [add_sub_cancel_left]
      rw [ENNReal.ofReal_div_of_pos hL, ENNReal.div_eq_inv_mul]
    have hratio : (if g.2 = 0 then (2 : ℝ) else 10) / (12 * (r : ℝ)) =
        phaseProb r g := by
      unfold phaseProb
      by_cases hg : g.2 = 0 <;> simp only [hg, ite_true, ite_false]
      all_goals field_simp [hrne] <;> ring
    exact hmass.trans (congrArg ENNReal.ofReal hratio)

end
end AronowAudit.P027.Wave1.UniformStart
