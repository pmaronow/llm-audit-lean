import AronowAudit.P001.Wave1.PdaMeanNotIdentifiedBlueprint
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N1

namespace AronowAudit.P001.Wave1.PdaMeanNotIdentified

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidablePdaMeanNotIdentifiedN2 (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma gapMarginal_eq_smul_restrict :
    gapMarginal = (1 / 2 : ℝ≥0∞) •
      volume.restrict (Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc (1 : ℝ) 2) := by
  unfold gapMarginal
  have hf : (fun x => ENNReal.ofReal (gapPDF x)) =
      (Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc (1 : ℝ) 2).indicator
        (fun _ => (1 / 2 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc (1 : ℝ) 2 <;>
      simp [gapPDF, Set.indicator, hx] <;> norm_num
  rw [hf, withDensity_indicator (measurableSet_Icc.union measurableSet_Icc),
    withDensity_const]

theorem n2_proof : N2 := by
  refine ⟨?_, ?_⟩
  · apply isProbabilityMeasure_iff.mpr
    rw [gapMarginal_eq_smul_restrict]
    simp only [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul, gap_support_volume]
    norm_num
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  · unfold gapMarginal
    apply (ae_withDensity_iff (ENNReal.measurable_ofReal.comp n1_proof.1)).mpr
    exact ae_of_all _ (fun x hx => by
      by_contra h
      apply hx
      exact ENNReal.ofReal_eq_zero.mpr (le_of_not_gt h))

end
end AronowAudit.P001.Wave1.PdaMeanNotIdentified
