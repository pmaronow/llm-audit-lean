import SAP.P001a.WH.W1.Leaves
import AronowAudit.P001.Wave1.Gap.WP001dB2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

universe u

namespace SAP.P001a.WH.W1.P.T8_L1

end SAP.P001a.WH.W1.P.T8_L1

theorem SAP.P001a.WH.W1.T8_L1_proof : SAP.P001a.WH.W1.T8_L1 := by
  intro A hA κ F G x hent hcross hpos
  let f : ℝ → ℝ := fun y => F.density x y
  let g : ℝ → ℝ := fun y => G.density x y
  have hf : Measurable f := by
    exact F.measurable.comp (measurable_const.prodMk measurable_id)
  have hg : Measurable g := by
    exact G.measurable.comp (measurable_const.prodMk measurable_id)
  have hfm : Measurable (fun y : ℝ => ENNReal.ofReal (f y)) := hf.ennreal_ofReal
  have hgm : Measurable (fun y : ℝ => ENNReal.ofReal (g y)) := hg.ennreal_ofReal
  have hFnorm : (∫⁻ y, ENNReal.ofReal (f y) ∂κ) = 1 := by
    have hprob : IsProbabilityMeasure (F.kernel x) := IsMarkovKernel.isProbabilityMeasure x
    have hm : (κ.withDensity (fun y => ENNReal.ofReal (f y))) Set.univ = 1 := by
      rw [← F.law x]
      exact hprob.measure_univ
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hm
  have hGnorm : (∫⁻ y, ENNReal.ofReal (g y) ∂κ) = 1 := by
    have hprob : IsProbabilityMeasure (G.kernel x) := IsMarkovKernel.isProbabilityMeasure x
    have hm : (κ.withDensity (fun y => ENNReal.ofReal (g y))) Set.univ = 1 := by
      rw [← G.law x]
      exact hprob.measure_univ
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hm
  have hcross' : Integrable (fun y => Real.log (g y))
      (κ.withDensity (fun y => ENNReal.ofReal (f y))) := by
    rw [← F.law x]
    exact hcross
  have hcrossκ : Integrable (fun y => f y * Real.log (g y)) κ := by
    have hi := (integrable_withDensity_iff hfm
      (ae_of_all κ (fun y => ENNReal.ofReal_lt_top))).mp hcross'
    simpa only [f, ENNReal.toReal_ofReal (F.nonnegative x _), smul_eq_mul, mul_comm] using hi
  have hdom0 : ∀ᵐ y ∂κ, ENNReal.ofReal (f y) ≠ 0 → 0 < g y := by
    have hp : ∀ᵐ y ∂(κ.withDensity (fun y => ENNReal.ofReal (f y))), 0 < g y := by
      rw [← F.law x]
      exact hpos
    exact (ae_withDensity_iff hfm).1 hp
  have hdom : ∀ᵐ y ∂κ, 0 < f y → 0 < g y := by
    filter_upwards [hdom0] with y hy hfy
    exact hy (ne_of_gt (ENNReal.ofReal_pos.mpr hfy))
  have hi : Integrable (fun y => f y * Real.log (f y) - f y * Real.log (g y)) κ := by
    exact hent.sub hcrossκ
  have hkl := AronowAudit.P001.Wave1.t8_section_kl κ f g hf hg
    (fun y => F.nonnegative x y) (fun y => G.nonnegative x y)
    hFnorm hGnorm hdom hi
  have hval : (∫ y, f y * Real.log (f y) - f y * Real.log (g y) ∂κ) =
      wholeSectionEntropy F x - ∫ y, Real.log (g y) ∂(F.kernel x) := by
    rw [integral_sub hent hcrossκ]
    change (∫ y, F.density x y * Real.log (F.density x y) ∂κ) -
        (∫ y, f y * Real.log (g y) ∂κ) =
      wholeSectionEntropy F x - ∫ y, Real.log (g y) ∂(F.kernel x)
    have hlog : (∫ y, Real.log (g y) ∂(F.kernel x)) =
        ∫ y, f y * Real.log (g y) ∂κ := by
      rw [F.law x, integral_withDensity_eq_integral_toReal_smul hfm
        (ae_of_all κ (fun y => ENNReal.ofReal_lt_top))]
      simp only [f, ENNReal.toReal_ofReal (F.nonnegative x _), smul_eq_mul]
    rw [hlog]
    rfl
  constructor
  · calc
      InformationTheory.klDiv (F.kernel x) (G.kernel x) =
          ENNReal.ofReal (∫ y, f y * Real.log (f y) - f y * Real.log (g y) ∂κ) := by
            rw [F.law x, G.law x]
            exact hkl.1
      _ = ENNReal.ofReal
          (wholeSectionEntropy F x - ∫ y, Real.log (G.density x y) ∂(F.kernel x)) := by
            rw [← hval]
  · rw [← hval]
    exact hkl.2
