import AronowAudit.P047.Wave1.Impossibility.N2
import AronowAudit.P047.Wave1.Impossibility.N6

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

/-- The fourth latent outcome/arm combination merges into the control record. -/
theorem n8_proof : N8 := by
  classical
  intro e m he hm heb hmb B hB
  let F : UnitData → ℝ := fun u => B.indicator (fun _ => (1 : ℝ)) (obsUnit u)
  have hF : Measurable F := (measurable_const.indicator hB).comp measurable_obsUnit
  have hi : Integrable F (genMeasure e m) := by
    apply Integrable.of_bound hF.aestronglyMeasurable 1
    apply ae_of_all
    intro u
    by_cases hu : obsUnit u ∈ B <;> simp [F, Set.indicator, hu]
  rw [← integral_indicator_one hB, integral_map measurable_obsUnit.aemeasurable
    (measurable_one.indicator hB).aestronglyMeasurable]
  change (∫ u, F u ∂genMeasure e m) = _
  rw [integral_genMeasure e m he hm heb hmb F hi]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    genQ, record, F, obsUnit, covariate, observed, arm, potential]
  norm_num <;> ring

end

end AronowAudit.P047.Wave1.Impossibility
