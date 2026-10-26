import AronowAudit.P046.Wave1.PropositionThreeBlueprint

set_option autoImplicit false

namespace AronowAudit.P046.Wave1.PropositionThree

open AronowAudit.P046 AronowAudit.P046.IntervalExample MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

noncomputable section

theorem n1_proof : N1 := by
  classical
  letI := IntervalExample.probability_continuity_mean.1
  have mw : Measurable W := measurable_fst
  have hle : covariateSigma ≤ (inferInstance : MeasurableSpace AronowAudit.P046.Unit) :=
    mw.comap_le
  letI : IsFiniteMeasure (IntervalExample.study.law.trim hle) := isFiniteMeasure_trim hle
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have mp : Measurable score := by
    exact measurable_const.ite measurableSet_Iic measurable_const
  have hp (w : ℝ) : 0 ≤ score w ∧ score w ≤ 1 := by
    unfold score
    split <;> norm_num
  have ix : Integrable X IntervalExample.study.law := by
    apply memLp_one_iff_integrable.1
      (memLp_of_bounded (a := 0) (b := 1) _ mx.aestronglyMeasurable 1)
    exact ae_of_all _ (fun o => by cases hx : o.2.1 <;> norm_num [X, bit, hx])
  have ip : Integrable (fun o => score (W o)) IntervalExample.study.law := by
    apply memLp_one_iff_integrable.1
      (memLp_of_bounded (a := 0) (b := 1) _ (mp.comp mw).aestronglyMeasurable 1)
    exact ae_of_all _ (fun o => hp (W o))
  have mps : Measurable[covariateSigma] (fun o => score (W o)) :=
    mp.comp (comap_measurable W)
  change condExp covariateSigma IntervalExample.study.law X =ᵐ[IntervalExample.study.law]
    fun o => score (W o)
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hle ix
    (fun _ _ _ => ip.integrableOn) ?_ mps.aestronglyMeasurable
  intro s hs _
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
  have hWB : MeasurableSet (W ⁻¹' B) := mw hB
  have mf : Measurable ((W ⁻¹' B).indicator X) := mx.indicator hWB
  have mg : Measurable ((W ⁻¹' B).indicator (fun o => score (W o))) :=
    (mp.comp mw).indicator hWB
  have ifg : Integrable
      (fun z => ((W ⁻¹' B).indicator X) (IntervalExample.generate z))
      (unitUniform.prod unitUniform) := by
    exact (ix.indicator hWB).comp_aemeasurable IntervalExample.measurable_generate.aemeasurable
  have hinner (w : ℝ) :
      (∫ u, ((W ⁻¹' B).indicator X) (IntervalExample.generate (w, u)) ∂unitUniform) =
        B.indicator score w := by
    by_cases hw : w ∈ B
    · simp only [Set.indicator_of_mem hw]
      have heq : (fun u => ((W ⁻¹' B).indicator X) (IntervalExample.generate (w, u))) =
          (fun u => bit (decide (u ≤ score w))) := by
        funext u
        simp [Set.indicator, IntervalExample.generate, W, X, hw]
      rw [heq, unitUniform_bernE (score w) (hp w).1 (hp w).2 bit]
      simp [bernE, bit]
    · have heq : (fun u => ((W ⁻¹' B).indicator X) (IntervalExample.generate (w, u))) =
          (fun _ => (0 : ℝ)) := by
        funext u
        simp [Set.indicator, IntervalExample.generate, W, hw]
      simp [heq, Set.indicator_of_notMem hw]
  have hggen : (fun z => ((W ⁻¹' B).indicator (fun o => score (W o)))
      (IntervalExample.generate z)) = (fun z : ℝ × ℝ => B.indicator score z.1) := by
    funext z
    by_cases h : z.1 ∈ B <;> simp [Set.indicator, IntervalExample.generate, W, h]
  rw [← integral_indicator hWB, ← integral_indicator hWB]
  change (∫ o, ((W ⁻¹' B).indicator (fun o => score (W o))) o
      ∂Measure.map IntervalExample.generate (unitUniform.prod unitUniform)) =
    ∫ o, ((W ⁻¹' B).indicator X) o
      ∂Measure.map IntervalExample.generate (unitUniform.prod unitUniform)
  rw [integral_map IntervalExample.measurable_generate.aemeasurable mg.aestronglyMeasurable,
    integral_map IntervalExample.measurable_generate.aemeasurable mf.aestronglyMeasurable,
    integral_prod _ ifg, hggen, integral_fun_fst]
  simp only [probReal_univ, one_smul, hinner]

end

end AronowAudit.P046.Wave1.PropositionThree
