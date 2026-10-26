import AronowAudit.P046.P046_Audit

namespace AronowAudit.P046.Wave1
noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open RegressionExample

private lemma RepairT4_score_measurable : Measurable score :=
  (measurable_of_countable scoreL).comp
    (measurable_threshold id (fun _ => (1/2 : ℝ)) measurable_id measurable_const)

private lemma RepairT4_prediction_measurable (theta : ℝ) : Measurable (prediction theta) :=
  (measurable_of_countable (predictionL theta)).comp
    (measurable_threshold id (fun _ => (1/2 : ℝ)) measurable_id measurable_const)

private lemma RepairT4_bounded_integrable {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsFiniteMeasure ν] (f : A → ℝ) (hf : Measurable f)
    (hr : ∀ a, 0 ≤ f a ∧ f a ≤ 1) : Integrable f ν :=
  memLp_one_iff_integrable.1
    (memLp_of_bounded (a := 0) (b := 1) (ae_of_all _ hr) hf.aestronglyMeasurable 1)

private lemma RepairT4_bern_range (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (f : Bool → ℝ) (hf : ∀ b, 0 ≤ f b ∧ f b ≤ 1) :
    0 ≤ bernE p f ∧ bernE p f ≤ 1 := by
  dsimp [bernE]
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hp.2) (hf false).1) (mul_nonneg hp.1 (hf true).1)
  · nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr (hf false).2),
      mul_nonneg hp.1 (sub_nonneg.mpr (hf true).2)]

/-- The conditional binary table is obtained from the actual three-uniform law. -/
private lemma RepairT4_table (f : Bool → Bool → ℝ)
    (hf : ∀ x y, 0 ≤ f x y ∧ f x y ≤ 1) :
    condExp covariateSigma study.law (fun o => f o.2.1 o.2.2.2) =ᵐ[study.law]
      fun o => bernE (score (W o)) (fun x => bernE (1/10)
        (fun z => f x (decide (W o ≤ (1/2 : ℝ)) && z))) := by
  let gen := RegressionExample.generate
  let ν := (unitUniform.prod unitUniform).prod unitUniform
  letI := probability_continuity_mean.1
  have mg : Measurable gen := measurable_generate
  have hle : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  letI : IsFiniteMeasure (study.law.trim hle) := isFiniteMeasure_trim hle
  let F : Unit → ℝ := fun o => f o.2.1 o.2.2.2
  let G : ℝ → ℝ := fun w => bernE (score w) (fun x => bernE (1/10)
    (fun z => f x (decide (w ≤ (1/2 : ℝ)) && z)))
  have ml : Measurable (fun w : ℝ => decide (w ≤ (1/2 : ℝ))) :=
    measurable_threshold id (fun _ => (1/2 : ℝ)) measurable_id measurable_const
  have mF : Measurable F :=
    (measurable_of_countable (Function.uncurry f)).comp
      (measurable_snd.fst.prodMk measurable_snd.snd.snd)
  have ms := RepairT4_score_measurable
  have mG : Measurable G := by
    dsimp [G, bernE]
    fun_prop
  have rG : ∀ w, 0 ≤ G w ∧ G w ≤ 1 := by
    intro w
    apply RepairT4_bern_range _ _ _ (fun x =>
      RepairT4_bern_range _ (by norm_num) _ (fun z => hf _ _))
    have hh := score_positivity (decide (w ≤ (1/2 : ℝ)))
    change 0 ≤ scoreL _ ∧ scoreL _ ≤ 1
    constructor <;> linarith
  have mGW : Measurable[covariateSigma] (fun o => G (W o)) := mG.comp (comap_measurable W)
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hle
    (RepairT4_bounded_integrable study.law F mF (fun o => hf _ _))
    (fun s _ _ => (RepairT4_bounded_integrable study.law _ (mG.comp measurable_fst)
      (fun o => rG _)).integrableOn) _ mGW.aestronglyMeasurable
  intro s hs _
  obtain ⟨t, ht, rfl⟩ := hs
  rw [← integral_indicator (ht.preimage (show Measurable W from measurable_fst)),
    ← integral_indicator (ht.preimage (show Measurable W from measurable_fst))]
  change (∫ o, (W ⁻¹' t).indicator (fun o => G (W o)) o ∂Measure.map gen ν) =
    ∫ o, (W ⁻¹' t).indicator F o ∂Measure.map gen ν
  erw [integral_map mg.aemeasurable ((mG.comp measurable_fst).indicator
    (ht.preimage measurable_fst)).aestronglyMeasurable,
    integral_map mg.aemeasurable (mF.indicator (ht.preimage measurable_fst)).aestronglyMeasurable]
  have hleft : (fun z => (W ⁻¹' t).indicator (fun o => G (W o)) (gen z)) =
      (fun z : (ℝ × ℝ) × ℝ => t.indicator G z.1.1) := rfl
  erw [hleft]
  change (∫ z : (ℝ × ℝ) × ℝ, t.indicator G z.1.1
    ∂((unitUniform.prod unitUniform).prod unitUniform)) = _
  rw [integral_fun_fst (fun z : ℝ × ℝ => t.indicator G z.1), integral_fun_fst (t.indicator G)]
  simp only [probReal_univ, one_smul]
  change (∫ w, t.indicator G w ∂unitUniform) = ∫ z, (W ⁻¹' t).indicator F (gen z) ∂ν
  have mH : Measurable (fun z => (W ⁻¹' t).indicator F (gen z)) :=
    (mF.indicator (ht.preimage measurable_fst)).comp mg
  have rH : ∀ z, 0 ≤ (W ⁻¹' t).indicator F (gen z) ∧
      (W ⁻¹' t).indicator F (gen z) ≤ 1 := by
    intro z
    by_cases h : W (gen z) ∈ t <;> simp [Set.indicator, h, F, hf]
  rw [integral_prod _ (RepairT4_bounded_integrable ν _ mH rH)]
  rw [integral_prod _ (RepairT4_bounded_integrable ν _ mH rH).integral_prod_left]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  change t.indicator G w = ∫ u, ∫ v,
    (W ⁻¹' t).indicator F (gen ((w,u),v)) ∂unitUniform ∂unitUniform
  by_cases hw : w ∈ t
  · simp only [Set.indicator_of_mem hw]
    have he (u v : ℝ) : (W ⁻¹' t).indicator F (gen ((w,u),v)) =
        f (decide (v ≤ score w)) (decide (w ≤ (1/2 : ℝ)) && decide (u ≤ (1/10 : ℝ))) := by
      have hz : gen ((w,u),v) ∈ W ⁻¹' t := hw
      exact Set.indicator_of_mem hz F
    have hp : 0 ≤ score w ∧ score w ≤ 1 := by
      have hh := score_positivity (decide (w ≤ (1/2 : ℝ)))
      change 0 ≤ scoreL _ ∧ scoreL _ ≤ 1
      constructor <;> linarith
    try simp_rw [he]
    have hv (u : ℝ) : (∫ v, f (decide (v ≤ score w))
        (decide (w ≤ (1/2 : ℝ)) && decide (u ≤ (1/10 : ℝ))) ∂unitUniform) =
        bernE (score w) (fun x => f x
          (decide (w ≤ (1/2 : ℝ)) && decide (u ≤ (1/10 : ℝ)))) :=
      unitUniform_bernE (score w) hp.1 hp.2
        (fun x => f x (decide (w ≤ (1/2 : ℝ)) && decide (u ≤ (1/10 : ℝ))))
    simp_rw [hv]
    rw [unitUniform_bernE (1/10) (by norm_num) (by norm_num)
      (fun z => bernE (score w) (fun x => f x (decide (w ≤ (1/2 : ℝ)) && z))) ]
    dsimp [G, bernE]
    ring
  · simp only [Set.indicator_of_notMem hw]
    have he (u v : ℝ) : (W ⁻¹' t).indicator F (gen ((w,u),v)) = 0 := by
      have hz : gen ((w,u),v) ∉ W ⁻¹' t := hw
      exact Set.indicator_of_notMem hz F
    simp_rw [he, integral_zero]

private lemma RepairT4_valid : ValidStudy study := by
  letI := probability_continuity_mean.1
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
  have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have hle : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  have hy : Y0 =ᵐ[study.law] Y1 := by
    apply (ae_map_iff measurable_generate.aemeasurable (measurableSet_eq_fun my0 my1)).2
    exact ae_of_all _ (fun _ => rfl)
  have hind : CondIndepFun covariateSigma hle Y1 X study.law := by
    classical
    apply (condIndepFun_iff_condExp_inter_preimage_eq_mul my1 mx).mpr
    intro s t hs ht
    let f1 : Bool → Bool → ℝ := fun _ y => if bit y ∈ s then 1 else 0
    let f2 : Bool → Bool → ℝ := fun x _ => if bit x ∈ t then 1 else 0
    let f : Bool → Bool → ℝ := fun x y => f1 x y * f2 x y
    have h := RepairT4_table f (fun x y => by dsimp [f, f1, f2]; split_ifs <;> norm_num)
    have h1 := RepairT4_table f1 (fun x y => by dsimp [f1]; split <;> norm_num)
    have h2 := RepairT4_table f2 (fun x y => by dsimp [f2]; split <;> norm_num)
    have he : (Y1 ⁻¹' s ∩ X ⁻¹' t).indicator (fun _ => (1 : ℝ)) =
        (fun o : Unit => f o.2.1 o.2.2.2) := by
      funext o
      by_cases hs' : bit o.2.2.2 ∈ s <;> by_cases ht' : bit o.2.1 ∈ t <;>
        simp [Set.indicator, Y1, X, f, f1, f2, hs', ht']
    have he1 : (Y1 ⁻¹' s).indicator (fun _ => (1 : ℝ)) =
        (fun o : Unit => f1 o.2.1 o.2.2.2) := by
      funext o
      simp only [Set.indicator, Set.mem_preimage, Y1, f1]
    have he2 : (X ⁻¹' t).indicator (fun _ => (1 : ℝ)) =
        (fun o : Unit => f2 o.2.1 o.2.2.2) := by
      funext o
      simp only [Set.indicator, Set.mem_preimage, X, f2]
    rw [he, he1, he2]
    filter_upwards [h, h1, h2] with o ho ho1 ho2
    rw [ho, ho1, ho2]
    dsimp [f, f1, f2, bernE]
    ring
  refine ⟨probability_continuity_mean.1, probability_continuity_mean.2.1,
    RepairT4_score_measurable, ?_, by norm_num [study],
    ae_of_all _ (fun o => score_positivity _), ?_, ?_, ?_, ?_, hind⟩
  · exact measurable_const.ite measurableSet_Iic measurable_const
  · have h := RepairT4_table (fun x _ => bit x) (fun x _ => by cases x <;> norm_num [bit])
    have he : (fun o : Unit => bernE (score (W o)) (fun x => bernE (1/10)
        (fun z => bit x))) = (fun o => score (W o)) := by
      funext o
      simp [bernE, bit]
    change condExp covariateSigma study.law (fun o => bit o.2.1) =ᵐ[study.law]
      (fun o => score (W o))
    rw [← he]
    exact h
  · have h := RepairT4_table (fun _ y => bit y) (fun _ y => by cases y <;> norm_num [bit])
    have he : (fun o : Unit => bernE (score (W o)) (fun _ => bernE (1/10)
        (fun z => bit (decide (W o ≤ (1/2 : ℝ)) && z)))) = (fun o => study.m (W o)) := by
      funext o
      change bernE (score (W o)) (fun _ => bernE (1/10)
        (fun z => bit (decide (W o ≤ (1/2 : ℝ)) && z))) =
        (if W o ≤ (1/2 : ℝ) then 1/10 else 0)
      simp [bernE, bit]
      split_ifs <;> ring
    change condExp covariateSigma study.law (fun o => bit o.2.2.2) =ᵐ[study.law]
      (fun o => study.m (W o))
    rw [← he]
    exact h
  · exact ae_of_all _ (fun o => by dsimp [study]; split <;> norm_num)
  · exact condIndepFun_congr_left covariateSigma study.law hle Y0 Y1 X my0 my1 mx hy hind

private lemma RepairT4_finite_memLp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Fintype B] [MeasurableSingletonClass B] (ν : Measure A) [IsFiniteMeasure ν] (f : B → ℝ)
    (g : A → B) (hg : Measurable g) (p : ℝ≥0∞) : MemLp (fun a => f (g a)) p ν := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun b => ‖f b‖)
  exact MemLp.of_bound ((measurable_of_countable f).comp hg).aestronglyMeasurable C
    (ae_of_all _ (fun a => hC (g a)))

/-- Finite-table integration is a pushforward calculation, with W still uniform. -/
private lemma RepairT4_integral (f : Unit → ℝ) (hf : Measurable f)
    (g : Bool → Bool → Bool → ℝ)
    (he : ∀ w u v, f (RegressionExample.generate ((w,u),v)) =
      g (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ))) (decide (v ≤ score w))) :
    (∫ o, f o ∂study.law) = atomE g := by
  let ν := (unitUniform.prod unitUniform).prod unitUniform
  have ml := measurable_threshold (fun z : (ℝ × ℝ) × ℝ => z.1.1) (fun _ => (1/2 : ℝ))
    measurable_fst.fst measurable_const
  have mz := measurable_threshold (fun z : (ℝ × ℝ) × ℝ => z.1.2) (fun _ => (1/10 : ℝ))
    measurable_fst.snd measurable_const
  have mx := measurable_threshold (fun z : (ℝ × ℝ) × ℝ => z.2) (fun z => score z.1.1)
    measurable_snd (RepairT4_score_measurable.comp measurable_fst.fst)
  have hi : Integrable (fun z : (ℝ × ℝ) × ℝ => f (RegressionExample.generate z)) ν := by
    have hb := RepairT4_finite_memLp ν (fun b : Bool × Bool × Bool => g b.1 b.2.1 b.2.2)
      (fun z => (decide (z.1.1 ≤ (1/2 : ℝ)), decide (z.1.2 ≤ (1/10 : ℝ)),
        decide (z.2 ≤ score z.1.1))) (ml.prodMk (mz.prodMk mx)) 1
    simpa only [he] using memLp_one_iff_integrable.1 hb
  change (∫ o, f o ∂Measure.map RegressionExample.generate ν) = _
  rw [integral_map measurable_generate.aemeasurable hf.aestronglyMeasurable,
    integral_prod _ hi, integral_prod _ hi.integral_prod_left]
  simp_rw [he]
  have hp (w : ℝ) : 0 ≤ score w ∧ score w ≤ 1 := by
    have hh := score_positivity (decide (w ≤ (1/2 : ℝ)))
    change 0 ≤ scoreL _ ∧ scoreL _ ≤ 1
    constructor <;> linarith
  have hv (w u : ℝ) :
      (∫ v, g (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ)))
        (decide (v ≤ score w)) ∂unitUniform) =
      bernE (score w) (g (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ)))) :=
    unitUniform_bernE (score w) (hp w).1 (hp w).2 _
  simp_rw [hv]
  have hu (w : ℝ) :
      (∫ u, bernE (score w) (g (decide (w ≤ (1/2 : ℝ)))
        (decide (u ≤ (1/10 : ℝ)))) ∂unitUniform) =
      bernE (1/10) (fun z => bernE (score w) (g (decide (w ≤ (1/2 : ℝ))) z)) :=
    unitUniform_bernE (1/10) (by norm_num) (by norm_num)
      (fun z => bernE (score w) (g (decide (w ≤ (1/2 : ℝ))) z))
  simp_rw [hu]
  change (∫ w, bernE (1/10) (fun z => bernE (scoreL (decide (w ≤ (1/2 : ℝ))))
    (fun x => g (decide (w ≤ (1/2 : ℝ))) z x)) ∂unitUniform) = _
  rw [unitUniform_bernE (1/2) (by norm_num) (by norm_num)
    (fun l => bernE (1/10) (fun z => bernE (scoreL l) (fun x => g l z x)))]
  norm_num [bernE, atomE, scoreL]
  ring

private def RepairT4_H (o : Unit) : ℝ := htTerm (study.pi (W o)) (X o) (Y o)
private def RepairT4_A (o : Unit) : ℝ :=
  adjustedTerm (study.pi (W o)) (X o) (Y o) (prediction 0 (W o))

private lemma RepairT4_Y_measurable : Measurable Y := by
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
  have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
  exact ((measurable_const.sub mx).mul my0).add (mx.mul my1)

private lemma RepairT4_H_measurable : Measurable RepairT4_H := by
  have mx : Measurable X := (measurable_of_countable bit).comp measurable_snd.fst
  exact (mx.mul RepairT4_Y_measurable).div (RepairT4_score_measurable.comp measurable_fst)

private lemma RepairT4_A_measurable : Measurable RepairT4_A := by
  have mx : Measurable X := (measurable_of_countable bit).comp measurable_snd.fst
  have mg := (RepairT4_prediction_measurable 0).comp (show Measurable W from measurable_fst)
  exact ((mx.mul (RepairT4_Y_measurable.sub mg)).div
    (RepairT4_score_measurable.comp measurable_fst)).add mg

private lemma RepairT4_H_L2 : MemLp RepairT4_H 2 study.law := by
  letI := probability_continuity_mean.1
  apply MemLp.of_bound RepairT4_H_measurable.aestronglyMeasurable 10
  apply ae_of_all
  rintro ⟨w,x,y0,y1⟩
  cases hl : decide (w ≤ (1/2 : ℝ)) <;> cases x <;> cases y0 <;> cases y1 <;>
    norm_num [RepairT4_H, study, score, scoreL, W, X, Y, Y0, Y1, bit, htTerm, hl]

private lemma RepairT4_A_L2 : MemLp RepairT4_A 2 study.law := by
  letI := probability_continuity_mean.1
  apply MemLp.of_bound RepairT4_A_measurable.aestronglyMeasurable 10
  apply ae_of_all
  rintro ⟨w,x,y0,y1⟩
  cases hl : decide (w ≤ (1/2 : ℝ)) <;> cases x <;> cases y0 <;> cases y1 <;>
    norm_num [RepairT4_A, study, score, scoreL, prediction, predictionL, W, X, Y, Y0, Y1,
      bit, adjustedTerm, hl]

private lemma RepairT4_H_generate (w u v : ℝ) :
    RepairT4_H (RegressionExample.generate ((w,u),v)) =
      H (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ))) (decide (v ≤ score w)) := by
  cases hl : decide (w ≤ (1/2 : ℝ)) <;> cases hz : decide (u ≤ (1/10 : ℝ)) <;>
    cases hx : decide (v ≤ score w) <;>
    simp only [RepairT4_H, H, RegressionExample.generate, study, W, X, Y, Y0, Y1, hl, hz, hx] <;>
    norm_num [htTerm, outcomeL, bit, score, scoreL, hl]

private lemma RepairT4_A_generate (w u v : ℝ) :
    RepairT4_A (RegressionExample.generate ((w,u),v)) =
      A (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ))) (decide (v ≤ score w)) := by
  cases hl : decide (w ≤ (1/2 : ℝ)) <;> cases hz : decide (u ≤ (1/10 : ℝ)) <;>
    cases hx : decide (v ≤ score w) <;>
    simp only [RepairT4_A, A, RegressionExample.generate, study, W, X, Y, Y0, Y1, hl, hz, hx] <;>
    norm_num [adjustedTerm, outcomeL, bit, score, scoreL, prediction, predictionL, hl]

private lemma RepairT4_H_mean : (∫ o, RepairT4_H o ∂study.law) = 1/20 := by
  rw [RepairT4_integral RepairT4_H RepairT4_H_measurable H RepairT4_H_generate]
  exact atom_moments.1

private lemma RepairT4_A_mean : (∫ o, RepairT4_A o ∂study.law) = 1/20 := by
  rw [RepairT4_integral RepairT4_A RepairT4_A_measurable A RepairT4_A_generate]
  exact atom_moments.2.1

private lemma RepairT4_H_variance : variance RepairT4_H study.law = 79/400 := by
  rw [variance_eq_integral RepairT4_H_measurable.aemeasurable, RepairT4_H_mean]
  rw [RepairT4_integral _ ((RepairT4_H_measurable.sub_const (1/20)).pow_const 2)
    (fun l z x => (H l z x - 1/20)^2)
    (fun w u v => by rw [RepairT4_H_generate])]
  exact atom_variances.1

private lemma RepairT4_A_variance : variance RepairT4_A study.law = 169/400 := by
  rw [variance_eq_integral RepairT4_A_measurable.aemeasurable, RepairT4_A_mean]
  rw [RepairT4_integral _ ((RepairT4_A_measurable.sub_const (1/20)).pow_const 2)
    (fun l z x => (A l z x - 1/20)^2)
    (fun w u v => by rw [RepairT4_A_generate])]
  exact atom_variances.2.1

private lemma RepairT4_norm (theta : ℝ) :
    weightedNormSq study (prediction theta) = 3/8 + theta^2/6 := by
  have mq : Measurable (fun o => q study (W o)) :=
    (measurable_const.sub (RepairT4_score_measurable.comp measurable_fst)).div
      (RepairT4_score_measurable.comp measurable_fst)
  unfold weightedNormSq
  rw [RepairT4_integral (fun o => q study (W o) * (prediction theta (W o))^2) (mq.mul
    (((RepairT4_prediction_measurable theta).comp measurable_fst).pow_const 2))
    (fun l _ _ => (1-scoreL l)/scoreL l * (predictionL theta l)^2) (by
      intro w u v
      rfl)]
  exact (zero_not_in_closure theta).1

private lemma RepairT4_risks : risk study (fun _ => 0) = 3/20 ∧
    risk study (prediction 0) = 3/8 := by
  have my1 : Measurable Y1 := (measurable_of_countable bit).comp measurable_snd.snd.snd
  have mq : Measurable (fun o => q study (W o)) :=
    (measurable_const.sub (RepairT4_score_measurable.comp measurable_fst)).div
      (RepairT4_score_measurable.comp measurable_fst)
  have hgen (w u v : ℝ) : Y1 (RegressionExample.generate ((w,u),v)) =
      outcomeL (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ))) := by
    cases hl : decide (w ≤ (1/2 : ℝ)) <;> cases hz : decide (u ≤ (1/10 : ℝ)) <;>
      norm_num [Y1, RegressionExample.generate, outcomeL, bit, hl, hz]
  constructor
  · unfold risk
    rw [RepairT4_integral (fun o => q study (W o) * (Y1 o - 0)^2)
      (mq.mul ((my1.sub (measurable_const (a := (0 : ℝ)))).pow_const 2))
      (fun l z _ => (1-scoreL l)/scoreL l * (outcomeL l z - 0)^2) (by
        intro w u v
        simp only [hgen]
        rfl)]
    norm_num [atomE, bernE, scoreL, outcomeL, bit]
  · unfold risk
    rw [RepairT4_integral (fun o => q study (W o) * (Y1 o - prediction 0 (W o))^2)
      (mq.mul ((my1.sub
        ((RepairT4_prediction_measurable 0).comp measurable_fst)).pow_const 2))
      (fun l z _ => (1-scoreL l)/scoreL l * (outcomeL l z - predictionL 0 l)^2) (by
        intro w u v
        simp only [hgen]
        rfl)]
    norm_num [atomE, bernE, scoreL, outcomeL, predictionL, bit]

private lemma RepairT4_adjusted_mean_form (n : ℕ) :
    adjusted study (fits n) = (fun a : Sample n => (∑ i, RepairT4_A (a i)) / n) := rfl

private lemma RepairT4_sample_results (n : ℕ) (hn : 0 < n) :
    (∫ a, ht study a ∂sampleLaw study n) = mu study ∧
    (∫ a, adjusted study (fits n) a ∂sampleLaw study n) = mu study ∧
    variance (ht study (n := n)) (sampleLaw study n) = 79/(400*n) ∧
    variance (adjusted study (fits n)) (sampleLaw study n) = 169/(400*n) := by
  letI := probability_continuity_mean.1
  have hm := probability_continuity_mean.2.2
  have hH := iid_mean_integral study.law RepairT4_H (RepairT4_H_L2.integrable (by norm_num)) n hn
  have hA := iid_mean_integral study.law RepairT4_A (RepairT4_A_L2.integrable (by norm_num)) n hn
  have vH := iid_mean_variance study.law RepairT4_H RepairT4_H_L2 n hn
  have vA := iid_mean_variance study.law RepairT4_A RepairT4_A_L2 n hn
  rw [RepairT4_H_mean, ← hm] at hH
  rw [RepairT4_A_mean, ← hm] at hA
  rw [RepairT4_H_variance] at vH
  rw [RepairT4_A_variance] at vA
  refine ⟨hH, ?_, ?_, ?_⟩
  · simpa only [RepairT4_adjusted_mean_form, sampleLaw] using hA
  · change variance (fun a : Sample n => (∑ i, RepairT4_H (a i)) / n)
      (Measure.pi (fun _ => study.law)) = _
    rw [vH]
    ring
  · rw [RepairT4_adjusted_mean_form]
    change variance (fun a : Sample n => (∑ i, RepairT4_A (a i)) / n)
      (Measure.pi (fun _ => study.law)) = _
    rw [vA]
    ring

private lemma RepairT4_normal_limits :
    NormalLimit study (fun _ => ht study) (79/400) ∧
    NormalLimit study (fun n => adjusted study (fits n)) (169/400) := by
  letI := probability_continuity_mean.1
  have hm := probability_continuity_mean.2.2
  constructor
  · refine ⟨probability_continuity_mean.1, ?_⟩
    have h := iid_mean_normal study.law RepairT4_H RepairT4_H_measurable RepairT4_H_L2
    rw [RepairT4_H_mean, ← hm, RepairT4_H_variance] at h
    exact h
  · refine ⟨probability_continuity_mean.1, ?_⟩
    have h := iid_mean_normal study.law RepairT4_A RepairT4_A_measurable RepairT4_A_L2
    rw [RepairT4_A_mean, ← hm, RepairT4_A_variance] at h
    simpa only [RepairT4_adjusted_mean_form, sampleLaw] using h

theorem regression_counterexample_proof : ValidStudy RegressionExample.study ∧ mu RegressionExample.study = 1/20 ∧
    Balanced RegressionExample.fits ∧ (∀ j, L2InProbability RegressionExample.study RegressionExample.fits j (RegressionExample.prediction 0)) ∧
    (∀ n j, ∀ᵐ a ∂sampleLaw RegressionExample.study n, ∀ theta,
      empiricalRisk RegressionExample.study (Finset.univ.filter (fun i => (RegressionExample.fits n).fold i ≠ j)) a (RegressionExample.prediction 0) ≤
      empiricalRisk RegressionExample.study (Finset.univ.filter (fun i => (RegressionExample.fits n).fold i ≠ j)) a (RegressionExample.prediction theta)) ∧
    (∀ n : ℕ, 0 < n →
      (∫ a, ht RegressionExample.study a ∂sampleLaw RegressionExample.study n) = mu RegressionExample.study ∧
      (∫ a, adjusted RegressionExample.study (RegressionExample.fits n) a ∂sampleLaw RegressionExample.study n) = mu RegressionExample.study ∧
      variance (ht RegressionExample.study (n := n)) (sampleLaw RegressionExample.study n) = 79/(400*n) ∧
      variance (adjusted RegressionExample.study (RegressionExample.fits n)) (sampleLaw RegressionExample.study n) = 169/(400*n)) ∧
    NormalLimit RegressionExample.study (fun _ => ht RegressionExample.study) (79/400) ∧
    NormalLimit RegressionExample.study (fun n => adjusted RegressionExample.study (RegressionExample.fits n)) (169/400) ∧
    (79/400 : ℝ) < 169/400 ∧
    (∀ theta, weightedNormSq RegressionExample.study (RegressionExample.prediction theta) = 3/8 + theta^2/6) ∧
    risk RegressionExample.study (fun _ => 0) = 3/20 ∧ risk RegressionExample.study (RegressionExample.prediction 0) = 3/8 := by
  exact ⟨RepairT4_valid, probability_continuity_mean.2.2, fits_balanced,
    fits_l2_convergence, fits_empirical_minimizer, RepairT4_sample_results,
    RepairT4_normal_limits.1, RepairT4_normal_limits.2, by norm_num,
    RepairT4_norm, RepairT4_risks.1, RepairT4_risks.2⟩

end
end AronowAudit.P046.Wave1
