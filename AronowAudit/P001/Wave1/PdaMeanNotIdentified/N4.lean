import AronowAudit.P001.Wave1.PdaMeanNotIdentifiedBlueprint

namespace AronowAudit.P001.Wave1.PdaMeanNotIdentified

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidablePdaMeanNotIdentifiedN4 (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma uniformLaw_neg_one_one_eq_smul_restrict :
    uniformLaw (-1) 1 = (1 / 2 : ℝ≥0∞) • volume.restrict (Set.Icc (-1 : ℝ) 1) := by
  unfold uniformLaw
  have hf : (fun x : ℝ => ENNReal.ofReal
      (if x ∈ Set.Icc (-1 : ℝ) 1 then (1 - (-1))⁻¹ else 0)) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 / 2 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;>
      simp [hx, Set.indicator] <;> norm_num
  rw [hf, withDensity_indicator measurableSet_Icc, withDensity_const]

theorem n4_proof : N4 := by
  refine ⟨?_, ?_⟩
  · apply isProbabilityMeasure_iff.mpr
    rw [uniformLaw_neg_one_one_eq_smul_restrict]
    simp only [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul, Real.volume_Icc]
    norm_num
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  · unfold uniformLaw
    have hm : Measurable (fun x : ℝ => ENNReal.ofReal
        (if x ∈ Set.Icc (-1 : ℝ) 1 then (1 - (-1))⁻¹ else 0)) :=
      ENNReal.measurable_ofReal.comp
        (Measurable.ite measurableSet_Icc measurable_const measurable_const)
    apply (ae_withDensity_iff hm).mpr
    exact ae_of_all _ (fun y hy => by
      by_contra h
      simp [h] at hy)

end
end AronowAudit.P001.Wave1.PdaMeanNotIdentified
