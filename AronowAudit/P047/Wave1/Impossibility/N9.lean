import AronowAudit.P047.Wave1.Impossibility.N6
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

theorem n9_proof : N9 := by
  classical
  intro B hB
  let b : ℝ × Bool × Bool → UnitData :=
    fun z => (z.1, z.2.1, (0, if z.2.2 then (1 : ℝ) else 0))
  let F : ℝ × Bool × Bool → ℝ :=
    fun z => B.indicator (fun _ => (1 : ℝ)) (obsUnit (b z))
  have hm : Measurable F :=
    ((measurable_const.indicator hB).comp measurable_obsUnit).comp measurable_baseline_map
  have hi : Integrable F (uniform01.prod (fairBool.prod fairBool)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    apply ae_of_all
    intro z
    by_cases hz : obsUnit (b z) ∈ B <;> simp [F, Set.indicator, hz]
  rw [← integral_indicator_one hB, integral_map measurable_obsUnit.aemeasurable
    (measurable_one.indicator hB).aestronglyMeasurable]
  rw [baselineLaw, integral_map measurable_baseline_map.aemeasurable
    (show Measurable (fun x : UnitData => B.indicator (1 : ObservedUnit → ℝ) (obsUnit x)) from
      (measurable_one.indicator hB).comp measurable_obsUnit).aestronglyMeasurable]
  change (∫ z, F z ∂uniform01.prod (fairBool.prod fairBool)) = _
  rw [integral_prod F hi]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  beta_reduce
  rw [integral_prod (fun z : Bool × Bool => F (w, z))
    (Integrable.of_finite : Integrable (fun z : Bool × Bool => F (w, z))
      (fairBool.prod fairBool))]
  simp only [fairBool, integral_bernoulliMeasure, smul_eq_mul]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    baseObs, record, F, b, obsUnit, covariate, observed, arm, potential]
  norm_num <;> ring

end

end AronowAudit.P047.Wave1.Impossibility
