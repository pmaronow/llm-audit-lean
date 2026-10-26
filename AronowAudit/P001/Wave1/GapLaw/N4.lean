import AronowAudit.P001.Wave1.GapLawBlueprint

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.GapLaw

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section

theorem n4_proof : N4 := by
  classical
  intro h1 h2
  obtain ⟨hprob, hXint, hYint, hXmean, hYmean, hXsupport, hYsupport⟩ := h1
  letI : IsProbabilityMeasure gapJointLaw := hprob
  have hXm : Measurable gapX := measurable_pi_lambda fun _ => measurable_fst
  have hcoord (j : Fin 1) : Integrable (fun ω => gapX ω j) gapJointLaw := hXint
  have hmapcoord (j : Fin 1) :
      Integrable (fun x : Fin 1 → ℝ => x j) (gapJointLaw.map gapX) := by
    apply (integrable_map_measure (measurable_pi_apply j).aestronglyMeasurable
      hXm.aemeasurable).mpr
    exact hcoord j
  have hmean : (fun j => ∫ x, x j ∂(gapJointLaw.map gapX)) = (0 : Fin 1 → ℝ) := by
    funext j
    rw [integral_map hXm.aemeasurable (measurable_pi_apply j).aestronglyMeasurable]
    exact hXmean
  have hmean0 : mean gapJointLaw (fun ω => gapX ω 0) = 0 := hXmean
  have hb : Measurable bumpVec :=
    h2.1.continuous.measurable.comp (measurable_pi_apply 0)
  have hae : (fun _ : Fin 1 → ℝ => (0 : ℝ)) =ᵐ[gapJointLaw.map gapX] bumpVec := by
    apply (ae_map_iff hXm.aemeasurable (measurableSet_eq_fun measurable_const hb)).mpr
    filter_upwards [hXsupport] with ω hω
    exact (h2.2.1 ω.1 hω.1).symm
  exact ⟨hXm, inferInstance, hmapcoord, hcoord, hmean, hmean0, hae⟩

end

end AronowAudit.P001.Wave1.GapLaw
