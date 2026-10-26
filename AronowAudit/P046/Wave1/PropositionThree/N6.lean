import AronowAudit.P046.Wave1.PropositionThreeBlueprint

set_option autoImplicit false

namespace AronowAudit.P046.Wave1.PropositionThree

open AronowAudit.P046 AronowAudit.P046.IntervalExample MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

noncomputable section

theorem n6_proof : N6 := by
  classical
  haveI := IntervalExample.probability_continuity_mean.1
  have my : Measurable (fun o : AronowAudit.P046.Unit => o.2.2) :=
    measurable_snd.snd
  have mt : Measurable (fun o : AronowAudit.P046.Unit =>
      (false, decide (o.1 ≤ (3 / 5 : ℝ)))) :=
    measurable_const.prodMk
      (measurable_threshold (fun o : AronowAudit.P046.Unit => o.1)
        (fun _ => (3 / 5 : ℝ)) measurable_fst measurable_const)
  have hu : ∀ᵐ o ∂IntervalExample.study.law,
      o.2.2 = (false, decide (o.1 ≤ (3 / 5 : ℝ))) := by
    change ∀ᵐ o ∂Measure.map IntervalExample.generate (unitUniform.prod unitUniform), _
    apply (ae_map_iff IntervalExample.measurable_generate.aemeasurable
      (measurableSet_eq_fun my mt)).2
    exact ae_of_all _ (fun _ => rfl)
  change ∀ᵐ a ∂Measure.pi (fun _ : Fin 100 => IntervalExample.study.law), _
  exact ae_all_iff.2 (fun i =>
    (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin 100 => IntervalExample.study.law) (i := i)).eventually hu)

end

end AronowAudit.P046.Wave1.PropositionThree
