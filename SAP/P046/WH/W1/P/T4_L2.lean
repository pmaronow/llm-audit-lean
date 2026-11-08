import SAP.P046.WH.W1.Leaves
import AronowAudit.P046.Wave1.Gap.GP046B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

namespace SAP.P046.WH.W1.P.T4_L2

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

lemma finite_memLp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Fintype B] [MeasurableSingletonClass B] (ν : Measure A) [IsFiniteMeasure ν]
    (f : B → ℝ) (g : A → B) (hg : Measurable g) (p : ℝ≥0∞) :
    MemLp (fun a => f (g a)) p ν := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun b => ‖f b‖)
  exact MemLp.of_bound ((measurable_of_countable f).comp hg).aestronglyMeasurable C
    (ae_of_all _ (fun a => hC (g a)))

def auditIntegrand (theta : ℝ) (o : AronowAudit.P046.Unit) : ℝ :=
  AronowAudit.P046.X o *
    (1 - AronowAudit.P046.RegressionExample.score (AronowAudit.P046.W o)) /
      (AronowAudit.P046.RegressionExample.score (AronowAudit.P046.W o)) ^ 2 *
    (AronowAudit.P046.Y o -
      AronowAudit.P046.RegressionExample.prediction theta (AronowAudit.P046.W o)) ^ 2

lemma auditScore_measurable :
    Measurable AronowAudit.P046.RegressionExample.score :=
  (measurable_of_countable AronowAudit.P046.RegressionExample.scoreL).comp
    (AronowAudit.P046.measurable_threshold id (fun _ => (1 / 2 : ℝ))
      measurable_id measurable_const)

lemma auditPrediction_measurable (theta : ℝ) :
    Measurable (AronowAudit.P046.RegressionExample.prediction theta) :=
  (measurable_of_countable (AronowAudit.P046.RegressionExample.predictionL theta)).comp
    (AronowAudit.P046.measurable_threshold id (fun _ => (1 / 2 : ℝ))
      measurable_id measurable_const)

lemma auditIntegrand_measurable (theta : ℝ) : Measurable (auditIntegrand theta) := by
  have mx : Measurable AronowAudit.P046.X :=
    (measurable_of_countable AronowAudit.P046.bit).comp measurable_snd.fst
  have my0 : Measurable AronowAudit.P046.Y0 :=
    (measurable_of_countable AronowAudit.P046.bit).comp measurable_snd.snd.fst
  have my1 : Measurable AronowAudit.P046.Y1 :=
    (measurable_of_countable AronowAudit.P046.bit).comp measurable_snd.snd.snd
  have my : Measurable AronowAudit.P046.Y :=
    ((measurable_const.sub mx).mul my0).add (mx.mul my1)
  have mw : Measurable (fun o : AronowAudit.P046.Unit =>
      AronowAudit.P046.RegressionExample.score (AronowAudit.P046.W o)) :=
    auditScore_measurable.comp measurable_fst
  have mg : Measurable (fun o : AronowAudit.P046.Unit =>
      AronowAudit.P046.RegressionExample.prediction theta (AronowAudit.P046.W o)) :=
    (auditPrediction_measurable theta).comp measurable_fst
  change Measurable (fun o : AronowAudit.P046.Unit =>
    AronowAudit.P046.X o *
      (1 - AronowAudit.P046.RegressionExample.score (AronowAudit.P046.W o)) /
      (AronowAudit.P046.RegressionExample.score (AronowAudit.P046.W o)) ^ 2 *
      (AronowAudit.P046.Y o - AronowAudit.P046.RegressionExample.prediction theta
        (AronowAudit.P046.W o)) ^ 2)
  exact ((mx.mul (measurable_const.sub mw)).div (mw.pow_const 2)).mul
    ((my.sub mg).pow_const 2)

lemma auditIntegrand_generate (theta : ℝ) (w u v : ℝ) :
    auditIntegrand theta (AronowAudit.P046.RegressionExample.generate ((w, u), v)) =
      AronowAudit.P046.RegressionExample.loss theta
        (decide (w ≤ (1 / 2 : ℝ))) (decide (u ≤ (1 / 10 : ℝ)))
        (decide (v ≤ AronowAudit.P046.RegressionExample.score w)) := by
  cases hl : decide (w ≤ (1 / 2 : ℝ)) <;>
    cases hz : decide (u ≤ (1 / 10 : ℝ)) <;>
    cases hx : decide (v ≤ AronowAudit.P046.RegressionExample.score w) <;>
    simp only [auditIntegrand, AronowAudit.P046.RegressionExample.generate,
      AronowAudit.P046.RegressionExample.prediction,
      AronowAudit.P046.RegressionExample.predictionL,
      AronowAudit.P046.RegressionExample.loss,
      AronowAudit.P046.RegressionExample.outcomeL,
      AronowAudit.P046.X, AronowAudit.P046.Y, AronowAudit.P046.Y0,
      AronowAudit.P046.Y1, AronowAudit.P046.W, AronowAudit.P046.bit, hl, hz, hx]
    <;> simp only [AronowAudit.P046.RegressionExample.score,
      AronowAudit.P046.RegressionExample.scoreL, hl]
    <;> norm_num <;> ring

lemma audit_integral_eq_atom (theta : ℝ) :
    (∫ o, auditIntegrand theta o ∂AronowAudit.P046.RegressionExample.study.law) =
      AronowAudit.P046.RegressionExample.atomE (AronowAudit.P046.RegressionExample.loss theta) := by
  letI := AronowAudit.P046.unitUniform_probability
  let ν : Measure ((ℝ × ℝ) × ℝ) :=
    (AronowAudit.P046.unitUniform.prod AronowAudit.P046.unitUniform).prod
      AronowAudit.P046.unitUniform
  let bmap : ((ℝ × ℝ) × ℝ) → Bool × Bool × Bool := fun z =>
    (decide (z.1.1 ≤ (1 / 2 : ℝ)), decide (z.1.2 ≤ (1 / 10 : ℝ)),
      decide (z.2 ≤ AronowAudit.P046.RegressionExample.score z.1.1))
  have mb : Measurable bmap := by
    exact (AronowAudit.P046.measurable_threshold
      (fun z : (ℝ × ℝ) × ℝ => z.1.1) (fun _ => (1 / 2 : ℝ))
      measurable_fst.fst measurable_const).prodMk
      ((AronowAudit.P046.measurable_threshold
        (fun z : (ℝ × ℝ) × ℝ => z.1.2) (fun _ => (1 / 10 : ℝ))
        measurable_fst.snd measurable_const).prodMk
        (AronowAudit.P046.measurable_threshold
          (fun z : (ℝ × ℝ) × ℝ => z.2)
          (fun z => AronowAudit.P046.RegressionExample.score z.1.1)
          measurable_snd (auditScore_measurable.comp measurable_fst.fst)))
  have hi : Integrable (fun z : (ℝ × ℝ) × ℝ =>
      auditIntegrand theta (AronowAudit.P046.RegressionExample.generate z)) ν := by
    have hfinite := finite_memLp ν
      (fun b : Bool × Bool × Bool =>
        AronowAudit.P046.RegressionExample.loss theta b.1 b.2.1 b.2.2) bmap mb 1
    have heq : (fun z : (ℝ × ℝ) × ℝ =>
        auditIntegrand theta (AronowAudit.P046.RegressionExample.generate z)) =
        fun z => AronowAudit.P046.RegressionExample.loss theta
          (bmap z).1 (bmap z).2.1 (bmap z).2.2 := by
      funext z
      exact auditIntegrand_generate theta z.1.1 z.1.2 z.2
    rw [heq]
    exact memLp_one_iff_integrable.1 hfinite
  change (∫ o, auditIntegrand theta o ∂Measure.map
    AronowAudit.P046.RegressionExample.generate ν) = _
  rw [integral_map AronowAudit.P046.RegressionExample.measurable_generate.aemeasurable
      (auditIntegrand_measurable theta).aestronglyMeasurable,
    integral_prod _ hi, integral_prod _ hi.integral_prod_left]
  have hp (w : ℝ) :
      0 ≤ AronowAudit.P046.RegressionExample.score w ∧
      AronowAudit.P046.RegressionExample.score w ≤ 1 := by
    have hh := AronowAudit.P046.RegressionExample.score_positivity
      (decide (w ≤ (1 / 2 : ℝ)))
    change 0 ≤ AronowAudit.P046.RegressionExample.scoreL _ ∧
      AronowAudit.P046.RegressionExample.scoreL _ ≤ 1
    constructor <;> linarith
  have hv (w u : ℝ) :
      (∫ v, AronowAudit.P046.RegressionExample.loss theta
          (decide (w ≤ (1 / 2 : ℝ))) (decide (u ≤ (1 / 10 : ℝ)))
          (decide (v ≤ AronowAudit.P046.RegressionExample.score w))
          ∂AronowAudit.P046.unitUniform) =
        AronowAudit.P046.bernE (AronowAudit.P046.RegressionExample.score w)
          (AronowAudit.P046.RegressionExample.loss theta
            (decide (w ≤ (1 / 2 : ℝ))) (decide (u ≤ (1 / 10 : ℝ)))) :=
    AronowAudit.P046.unitUniform_bernE _ (hp w).1 (hp w).2 _
  simp_rw [auditIntegrand_generate, hv]
  have hu (w : ℝ) :
      (∫ u, AronowAudit.P046.bernE (AronowAudit.P046.RegressionExample.score w)
          (AronowAudit.P046.RegressionExample.loss theta
            (decide (w ≤ (1 / 2 : ℝ))) (decide (u ≤ (1 / 10 : ℝ))))
          ∂AronowAudit.P046.unitUniform) =
        AronowAudit.P046.bernE (1 / 10) (fun z =>
          AronowAudit.P046.bernE (AronowAudit.P046.RegressionExample.score w)
            (AronowAudit.P046.RegressionExample.loss theta
              (decide (w ≤ (1 / 2 : ℝ))) z)) :=
    AronowAudit.P046.unitUniform_bernE (1 / 10) (by norm_num) (by norm_num)
      (fun z => AronowAudit.P046.bernE (AronowAudit.P046.RegressionExample.score w)
        (AronowAudit.P046.RegressionExample.loss theta
          (decide (w ≤ (1 / 2 : ℝ))) z))
  simp_rw [hu]
  change (∫ w, AronowAudit.P046.bernE (1 / 10) (fun z =>
    AronowAudit.P046.bernE
      (AronowAudit.P046.RegressionExample.scoreL (decide (w ≤ (1 / 2 : ℝ))))
      (AronowAudit.P046.RegressionExample.loss theta
        (decide (w ≤ (1 / 2 : ℝ))) z)) ∂AronowAudit.P046.unitUniform) = _
  rw [AronowAudit.P046.unitUniform_bernE (1 / 2) (by norm_num) (by norm_num)
    (fun l => AronowAudit.P046.bernE (1 / 10) (fun z =>
      AronowAudit.P046.bernE (AronowAudit.P046.RegressionExample.scoreL l)
        (AronowAudit.P046.RegressionExample.loss theta l z)))]
  norm_num [AronowAudit.P046.RegressionExample.atomE,
    AronowAudit.P046.RegressionExample.score,
    AronowAudit.P046.RegressionExample.scoreL,
    AronowAudit.P046.bernE]
  ring

end
end SAP.P046.WH.W1.P.T4_L2

theorem SAP.P046.WH.W1.T4_L2_proof : SAP.P046.WH.W1.T4_L2 := by
  intro theta
  letI := AronowAudit.P046.RegressionExample.probability_continuity_mean.1
  have hvalidSAP : SAP.P046.ValidStudy SAP.P046.RegressionExample.study :=
    SAP.P046.Bridge.target4.1
  have hvalidAudit : AronowAudit.P046.ValidStudy
      AronowAudit.P046.RegressionExample.study := by
    rw [← SAP.P046.Bridge.regression_study]
    exact SAP.P046.Bridge.valid_to hvalidSAP
  have prediction_memLp (t : ℝ) : MemLp (fun o : AronowAudit.P046.Unit =>
      AronowAudit.P046.RegressionExample.prediction t (AronowAudit.P046.W o)) 2
      AronowAudit.P046.RegressionExample.study.law := by
    have mp : Measurable (fun o : AronowAudit.P046.Unit =>
        AronowAudit.P046.RegressionExample.prediction t (AronowAudit.P046.W o)) :=
      SAP.P046.WH.W1.P.T4_L2.auditPrediction_measurable t |>.comp measurable_fst
    have hb : ∀ o, ‖AronowAudit.P046.RegressionExample.prediction t
        (AronowAudit.P046.W o)‖ ≤ max ‖(1 / 2 : ℝ)‖ ‖t‖ := by
      intro o
      rw [AronowAudit.P046.RegressionExample.prediction,
        AronowAudit.P046.RegressionExample.predictionL]
      split <;> simp <;> first | exact le_max_left _ _ | exact le_max_right _ _
    exact MemLp.of_bound mp.aestronglyMeasurable _ (ae_of_all _ hb)
  have hg := prediction_memLp theta
  have hcriterion := AronowAudit.P046.Wave1.population_weighted_criterion_proof
    AronowAudit.P046.RegressionExample.study hvalidAudit
    (fun w => AronowAudit.P046.RegressionExample.prediction theta w) hg
  have hcriterionWhole : (∫ o, SAP.P046.WH.W1.P.T4_L2.auditIntegrand theta o
      ∂AronowAudit.P046.RegressionExample.study.law) =
      AronowAudit.P046.risk AronowAudit.P046.RegressionExample.study
        (fun w => AronowAudit.P046.RegressionExample.prediction theta w) := by
    calc
      _ = ∫ o, AronowAudit.P046.X o *
          (1 - AronowAudit.P046.RegressionExample.score (AronowAudit.P046.W o)) /
            (AronowAudit.P046.RegressionExample.score (AronowAudit.P046.W o)) ^ 2 *
          (AronowAudit.P046.Y o - AronowAudit.P046.RegressionExample.prediction theta
            (AronowAudit.P046.W o)) ^ 2 ∂AronowAudit.P046.RegressionExample.study.law := by
            rfl
      _ = _ := by
        simpa only [AronowAudit.P046.RegressionExample.study] using hcriterion
  have hactualAudit := hcriterionWhole
  have hpolyAudit (t : ℝ) : AronowAudit.P046.risk AronowAudit.P046.RegressionExample.study
      (fun w => AronowAudit.P046.RegressionExample.prediction t w) = 3 / 8 + t ^ 2 / 6 := by
    have hc := AronowAudit.P046.Wave1.population_weighted_criterion_proof
      AronowAudit.P046.RegressionExample.study hvalidAudit
      (fun w => AronowAudit.P046.RegressionExample.prediction t w) (prediction_memLp t)
    have ha : (∫ o, SAP.P046.WH.W1.P.T4_L2.auditIntegrand t o
        ∂AronowAudit.P046.RegressionExample.study.law) =
        AronowAudit.P046.risk AronowAudit.P046.RegressionExample.study
          (fun w => AronowAudit.P046.RegressionExample.prediction t w) := by
      calc
        _ = ∫ o, AronowAudit.P046.X o *
            (1 - AronowAudit.P046.RegressionExample.score (AronowAudit.P046.W o)) /
              (AronowAudit.P046.RegressionExample.score (AronowAudit.P046.W o)) ^ 2 *
            (AronowAudit.P046.Y o - AronowAudit.P046.RegressionExample.prediction t
              (AronowAudit.P046.W o)) ^ 2 ∂AronowAudit.P046.RegressionExample.study.law := rfl
        _ = _ := by simpa only [AronowAudit.P046.RegressionExample.study] using hc
    rw [← ha, SAP.P046.WH.W1.P.T4_L2.audit_integral_eq_atom]
    exact AronowAudit.P046.RegressionExample.population_loss t
  have hactual :
      (∫ o, SAP.P046.X o * SAP.P046.wholeWeight (SAP.P046.W o) *
        (SAP.P046.Y o - SAP.P046.RegressionExample.prediction theta
          (SAP.P046.W o)) ^ 2 ∂SAP.P046.RegressionExample.study.law) =
        SAP.P046.risk SAP.P046.RegressionExample.study
          (SAP.P046.RegressionExample.prediction theta) := by
    change (∫ o : AronowAudit.P046.Unit, SAP.P046.X o *
      SAP.P046.wholeWeight (SAP.P046.W o) *
      (SAP.P046.Y o - SAP.P046.RegressionExample.prediction theta (SAP.P046.W o)) ^ 2
      ∂AronowAudit.P046.RegressionExample.study.law) =
        AronowAudit.P046.risk AronowAudit.P046.RegressionExample.study
          (fun w => AronowAudit.P046.RegressionExample.prediction theta w)
    calc
      _ = ∫ o, SAP.P046.WH.W1.P.T4_L2.auditIntegrand theta o
          ∂AronowAudit.P046.RegressionExample.study.law := by
        apply integral_congr_ae
        filter_upwards [] with o
        cases hl : decide (AronowAudit.P046.W o ≤ (1 / 2 : ℝ)) <;>
          cases hx : o.2.1 <;>
          simp [SAP.P046.wholeWeight, SAP.P046.RegressionExample.score,
            SAP.P046.RegressionExample.scoreL, SAP.P046.RegressionExample.prediction,
            SAP.P046.RegressionExample.predictionL, SAP.P046.X, SAP.P046.Y,
            SAP.P046.Y0, SAP.P046.Y1, SAP.P046.W, SAP.P046.bit,
            SAP.P046.WH.W1.P.T4_L2.auditIntegrand,
            AronowAudit.P046.RegressionExample.score,
            AronowAudit.P046.RegressionExample.scoreL,
            AronowAudit.P046.RegressionExample.prediction,
            AronowAudit.P046.RegressionExample.predictionL,
            AronowAudit.P046.X, AronowAudit.P046.Y, AronowAudit.P046.Y0,
            AronowAudit.P046.Y1, AronowAudit.P046.W, AronowAudit.P046.bit, hl, hx]
          <;> norm_num <;> ring
      _ = _ := hactualAudit
  have hpoly : ∀ t, SAP.P046.risk SAP.P046.RegressionExample.study
      (SAP.P046.RegressionExample.prediction t) = 3 / 8 + t ^ 2 / 6 := by
    intro t
    change AronowAudit.P046.risk AronowAudit.P046.RegressionExample.study
      (fun w => AronowAudit.P046.RegressionExample.prediction t w) = 3 / 8 + t ^ 2 / 6
    exact hpolyAudit t
  refine ⟨hactual, hpoly theta, ?_⟩
  rw [hpoly theta, hpoly 0]
  constructor
  · intro h
    nlinarith [sq_nonneg theta]
  · intro h
    simp [h]
