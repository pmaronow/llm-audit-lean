import AronowAudit.P046.Wave1.PropositionThreeBlueprint

set_option autoImplicit false

namespace AronowAudit.P046.Wave1.PropositionThree

open AronowAudit.P046 AronowAudit.P046.IntervalExample MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

noncomputable section

theorem n2_proof : N2 := by
  classical
  intro hprop
  letI := IntervalExample.probability_continuity_mean.1
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
  have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have mw : Measurable W := measurable_fst
  have hle : covariateSigma ≤ (inferInstance : MeasurableSpace AronowAudit.P046.Unit) :=
    mw.comap_le
  letI : IsFiniteMeasure (IntervalExample.study.law.trim hle) := isFiniteMeasure_trim hle
  let r : AronowAudit.P046.Unit → ℝ := fun o => bit (decide (W o ≤ (3 / 5 : ℝ)))
  have mt : Measurable (fun w : ℝ => bit (decide (w ≤ (3 / 5 : ℝ)))) :=
    mb.comp (measurable_threshold id (fun _ : ℝ => (3 / 5 : ℝ))
      measurable_id measurable_const)
  have mr : Measurable r := mt.comp mw
  have mrs : Measurable[covariateSigma] r := mt.comp (comap_measurable W)
  have hr : Integrable r IntervalExample.study.law := by
    apply memLp_one_iff_integrable.1
      (memLp_of_bounded (a := 0) (b := 1) _ mr.aestronglyMeasurable 1)
    exact ae_of_all _ (fun o => by
      dsimp [r]
      cases decide (W o ≤ (3 / 5 : ℝ)) <;> norm_num [bit])
  have hz : Y0 =ᵐ[IntervalExample.study.law] fun _ => (0 : ℝ) := by
    change ∀ᵐ o ∂Measure.map IntervalExample.generate (unitUniform.prod unitUniform), Y0 o = 0
    apply (ae_map_iff IntervalExample.measurable_generate.aemeasurable
      (measurableSet_eq_fun my0 measurable_const)).2
    exact ae_of_all _ (fun _ => by simp [IntervalExample.generate, Y0, bit])
  have hy : Y1 =ᵐ[IntervalExample.study.law] r := by
    change ∀ᵐ o ∂Measure.map IntervalExample.generate (unitUniform.prod unitUniform), Y1 o = r o
    apply (ae_map_iff IntervalExample.measurable_generate.aemeasurable
      (measurableSet_eq_fun my1 mr)).2
    exact ae_of_all _ (fun _ => rfl)
  refine ⟨IntervalExample.probability_continuity_mean.1,
    IntervalExample.probability_continuity_mean.2.1, ?_, ?_, ?_, ?_, hprop, ?_, ?_, ?_, ?_⟩
  · change Measurable score
    exact measurable_const.ite measurableSet_Iic measurable_const
  · change Measurable (fun w : ℝ => if w ≤ (3 / 5 : ℝ) then (1 : ℝ) else 0)
    exact measurable_const.ite measurableSet_Iic measurable_const
  · norm_num [IntervalExample.study]
  · exact ae_of_all _ (fun o => score_positivity (W o))
  · calc
      condExp covariateSigma IntervalExample.study.law Y1 =ᵐ[IntervalExample.study.law]
          condExp covariateSigma IntervalExample.study.law r := condExp_congr_ae hy
      _ = _ := by
        rw [condExp_of_stronglyMeasurable hle mrs.stronglyMeasurable hr]
        funext o
        simp [r, IntervalExample.study, bit]
  · exact ae_of_all _ (fun o => by dsimp [IntervalExample.study]; split <;> norm_num)
  · exact condIndepFun_congr_left covariateSigma IntervalExample.study.law hle
      Y0 (fun _ => 0) X my0 measurable_const mx hz (condIndepFun_const_left 0 X)
  · exact condIndepFun_congr_left covariateSigma IntervalExample.study.law hle
      Y1 r X my1 mr mx hy (condIndepFun_of_measurable_left mrs mx)

end

end AronowAudit.P046.Wave1.PropositionThree
