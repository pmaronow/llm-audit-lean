import AronowAudit.P001.Wave1.PdaMeanNotIdentifiedBlueprint
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N1
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N4

namespace AronowAudit.P001.Wave1.PdaMeanNotIdentified

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidablePdaMeanNotIdentifiedN5 (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem n5_proof : N5 := by
  let g : ℝ → ℝ := fun y => if y ∈ Set.Icc (-1 : ℝ) 1 then 1 / 2 else 0
  have hg : Measurable g :=
    Measurable.ite measurableSet_Icc measurable_const measurable_const
  have hg0 : ∀ y, 0 ≤ g y := by
    intro y
    dsimp [g]
    split_ifs <;> norm_num
  have hgi : Integrable g volume := by
    have heq : g = (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 / 2 : ℝ)) := by
      funext y
      by_cases hy : y ∈ Set.Icc (-1 : ℝ) 1
      · rw [Set.indicator_of_mem hy]; exact if_pos hy
      · rw [Set.indicator_of_notMem hy]; exact if_neg hy
    rw [heq]
    apply IntegrableOn.integrable_indicator _ measurableSet_Icc
    exact integrableOn_const (by rw [Real.volume_Icc]; norm_num)
  have hu : uniformLaw (-1) 1 = volume.withDensity (fun y => ENNReal.ofReal (g y)) := by
    unfold uniformLaw
    congr 1
    funext y
    dsimp [g]
    split_ifs <;> norm_num
  change HasJointPDF gapJointLaw (fun xy => gapPDF xy.1 * g xy.2)
  refine ⟨((n1_proof.1.comp measurable_fst).mul (hg.comp measurable_snd)).aemeasurable,
    fun xy => mul_nonneg (n1_proof.2.1 _) (hg0 _), ?_, ?_⟩
  · rw [Measure.volume_eq_prod]
    exact n1_proof.2.2.1.mul_prod hgi
  · unfold gapJointLaw
    rw [hu, prod_withDensity (f := fun x => ENNReal.ofReal (gapPDF x))
      (g := fun y => ENNReal.ofReal (g y)) (ENNReal.measurable_ofReal.comp n1_proof.1)
      (ENNReal.measurable_ofReal.comp hg), Measure.volume_eq_prod]
    apply withDensity_congr_ae
    exact ae_of_all _ (fun xy => (ENNReal.ofReal_mul (n1_proof.2.1 _)).symm)

end
end AronowAudit.P001.Wave1.PdaMeanNotIdentified
