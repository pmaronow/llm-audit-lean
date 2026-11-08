import Mathlib
import SAP.P046.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P046.WH.W2.P.T8_L4

noncomputable section

open MeasureTheory ProbabilityTheory
open SAP.P046.WH.W2.P.T8_L4
open SAP.P046 SAP.P046.WH.W2
open scoped ENNReal

lemma condExp_mul_of_condIndep {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : @Measure Ω mΩ} [IsFiniteMeasure μ] {m' : MeasurableSpace Ω}
    (hm : m' ≤ mΩ) (f g : Ω → ℝ)
    (hf : @Measurable Ω ℝ mΩ Real.measurableSpace f)
    (hg : @Measurable Ω ℝ mΩ Real.measurableSpace g)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hfint : Integrable f μ) (hgint : Integrable g μ)
    (hind : CondIndepFun (m' := m') (mΩ := mΩ) (hm' := hm) (μ := μ) f g) :
    condExp m' μ (fun x => f x * g x) =ᵐ[μ]
      fun x => condExp m' μ f x * condExp m' μ g x := by
  let κ := condExpKernel (mΩ := mΩ) μ m'
  have hmap := (condIndepFun_iff_map_prod_eq_prod_map_map (μ := μ) (m' := m')
    (mΩ := mΩ) (hm' := hm) hf hg).mp hind
  have hker : (fun x => ∫ z, f z * g z ∂κ x) =ᵐ[μ.trim hm]
      fun x => (∫ z, f z ∂κ x) * (∫ z, g z ∂κ x) := by
    filter_upwards [hmap] with x hx
    have hmul : Measurable (fun z : ℝ × ℝ => z.1 * z.2) := measurable_fst.mul measurable_snd
    calc
      ∫ z, f z * g z ∂κ x =
          ∫ z, z.1 * z.2 ∂(κ.map (fun y => (f y, g y)) x) := by
            symm
            rw [Kernel.map_apply _ (hf.prodMk hg) x]
            exact integral_map ((hf.prodMk hg).aemeasurable) hmul.aestronglyMeasurable
      _ = ∫ z, z.1 * z.2 ∂((κ.map f x).prod (κ.map g x)) := by
            rw [hx, Kernel.prod_apply]
      _ = (∫ z, z ∂(κ.map f x)) * (∫ z, z ∂(κ.map g x)) := by
            simpa using (integral_prod_mul (fun z : ℝ => z) (fun z : ℝ => z)
              (μ := (κ.map f x)) (ν := (κ.map g x)))
      _ = (∫ z, f z ∂κ x) * (∫ z, g z ∂κ x) := by
            rw [Kernel.map_apply _ hf x, Kernel.map_apply _ hg x,
              integral_map hf.aemeasurable (by fun_prop),
              integral_map hg.aemeasurable (by fun_prop)]
  have hker' : (fun x => ∫ z, f z * g z ∂κ x) =ᵐ[μ]
      fun x => (∫ z, f z ∂κ x) * (∫ z, g z ∂κ x) := by
    have hsm1 : StronglyMeasurable[m'] (fun x => ∫ z, f z * g z ∂κ x) :=
      MeasureTheory.StronglyMeasurable.integral_condExpKernel (m := m') (mΩ := mΩ)
        (hf.mul hg).stronglyMeasurable
    have hsm2 : StronglyMeasurable[m'] (fun x =>
        (∫ z, f z ∂κ x) * (∫ z, g z ∂κ x)) :=
      (MeasureTheory.StronglyMeasurable.integral_condExpKernel (m := m') (mΩ := mΩ)
        hf.stronglyMeasurable).mul
        (MeasureTheory.StronglyMeasurable.integral_condExpKernel (m := m') (mΩ := mΩ)
          hg.stronglyMeasurable)
    exact (hsm1.ae_eq_trim_iff hm hsm2).mp (by simpa [κ] using hker)
  have hcefg := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel (mΩ := mΩ) hm hfg
  have hcef := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel (mΩ := mΩ) hm hfint
  have hceg := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel (mΩ := mΩ) hm hgint
  filter_upwards [hcefg, hcef, hceg, hker'] with x h1 h2 h3 h4
  rw [h1, h4, h2, h3]

lemma integral_eval_preimage (M : Study) (hprob : IsProbabilityMeasure M.law)
    (n : ℕ) (i : Fin n) (t : Set ℝ) (ht : MeasurableSet t)
    (f : Unit → ℝ) (hf : Integrable f M.law) :
    ∫ a in {a : Sample n | W (a i) ∈ t}, f (a i) ∂sampleLaw M n =
      ∫ o in W ⁻¹' t, f o ∂M.law := by
  letI := hprob
  let e : Sample n → Unit := fun a => a i
  let U : Set Unit := W ⁻¹' t
  have hU : MeasurableSet U := ht.preimage measurable_fst
  have hS : MeasurableSet (e ⁻¹' U) := hU.preimage (measurable_pi_apply i)
  have hS_eq : e ⁻¹' U = {a : Sample n | W (a i) ∈ t} := by
    ext a
    rfl
  have hp : MeasurePreserving e (sampleLaw M n) M.law :=
    measurePreserving_eval (fun _ : Fin n => M.law) i
  have hfi : Integrable (U.indicator f) (Measure.map e (sampleLaw M n)) := by
    rw [hp.map_eq]
    exact hf.indicator hU
  calc
    _ = ∫ a in e ⁻¹' U, f (e a) ∂sampleLaw M n := by rw [hS_eq]
    _ = ∫ a, (e ⁻¹' U).indicator (fun a => f (e a)) a ∂sampleLaw M n :=
      (integral_indicator hS).symm
    _ = ∫ a, (U.indicator f) (e a) ∂sampleLaw M n := by
      congr 1
    _ = ∫ o, U.indicator f o ∂Measure.map e (sampleLaw M n) :=
      (integral_map hp.measurable.aemeasurable hfi.aestronglyMeasurable).symm
    _ = ∫ o in U, f o ∂M.law := by
      rw [hp.map_eq, integral_indicator hU]

lemma unit_X_integrable (M : Study) (hM : ValidStudy M) : Integrable X M.law := by
  letI := hM.probability
  have hmeas : Measurable X := (measurable_of_countable bit).comp measurable_snd.fst
  have hbound : ∀ o, X o ∈ Set.Icc (0 : ℝ) 1 := by
    intro o
    rcases o with ⟨w, x, y0, y1⟩
    cases x <;> norm_num [X, bit]
  exact memLp_one_iff_integrable.mp
    (memLp_of_bounded (Filter.Eventually.of_forall hbound) hmeas.aestronglyMeasurable 1)

lemma unit_pi_integrable (M : Study) (hM : ValidStudy M) :
    Integrable (fun o => M.pi (W o)) M.law := by
  letI := hM.probability
  have hmeas : Measurable (fun o => M.pi (W o)) := hM.measurable_pi.comp measurable_fst
  have hbound : ∀ᵐ o ∂M.law, M.pi (W o) ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hM.positivity] with o ho
    exact ⟨(hM.delta_pos.trans ho.1).le, (ho.2.trans (by linarith [hM.delta_pos])).le⟩
  exact memLp_one_iff_integrable.mp (memLp_of_bounded hbound hmeas.aestronglyMeasurable 1)

lemma eval_propensity (M : Study) (hM : ValidStudy M) (n : ℕ) (i : Fin n) :
    condExp (wholeOwnSigma n i) (sampleLaw M n) (fun a => X (a i)) =ᵐ[sampleLaw M n]
      fun a => M.pi (W (a i)) := by
  letI := hM.probability
  let μ := sampleLaw M n
  let e : Sample n → Unit := fun a => a i
  let q : Sample n → ℝ := fun a => M.pi (W (a i))
  let x : Sample n → ℝ := fun a => X (a i)
  have hm : wholeOwnSigma n i ≤ (inferInstance : MeasurableSpace (Sample n)) :=
    (measurable_fst.comp (measurable_pi_apply i)).comap_le
  have hp : MeasurePreserving e μ M.law :=
    measurePreserving_eval (fun _ : Fin n => M.law) i
  have hxint : Integrable x μ := by
    exact hp.integrable_comp_of_integrable (unit_X_integrable M hM)
  have hqint : Integrable q μ := by
    exact hp.integrable_comp_of_integrable (unit_pi_integrable M hM)
  have hqsm : StronglyMeasurable[wholeOwnSigma n i] q := by
    letI : MeasurableSpace (Sample n) := wholeOwnSigma n i
    exact (hM.measurable_pi.comp (comap_measurable (fun a : Sample n => W (a i)))).stronglyMeasurable
  letI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hxint
  · intro s hs hsfin
    exact hqint.integrableOn
  · intro s hs hsfin
    rcases (MeasurableSpace.measurableSet_comap.mp (by simpa [wholeOwnSigma] using hs)) with
      ⟨t, ht, hseq⟩
    have hset : {a : Sample n | W (a i) ∈ t} =
        (fun a : Sample n => W (a i)) ⁻¹' t := by
      ext a
      rfl
    let U : Set Unit := W ⁻¹' t
    have hU : MeasurableSet U := ht.preimage measurable_fst
    have hUown : @MeasurableSet Unit covariateSigma U := by
      exact ht.preimage (comap_measurable W)
    have hsingle : (∫ o in U, X o ∂M.law) = ∫ o in U, M.pi (W o) ∂M.law := by
      calc
        _ = ∫ o in U, condExp covariateSigma M.law X o ∂M.law :=
          (setIntegral_condExp (hm := measurable_fst.comap_le)
            (unit_X_integrable M hM) hUown).symm
        _ = _ := setIntegral_congr_ae hU (by
          filter_upwards [hM.propensity] with o ho
          intro _
          exact ho)
    calc
      ∫ a in s, q a ∂μ = ∫ a in {a : Sample n | W (a i) ∈ t}, q a ∂μ := by
        rw [← hseq, hset]
      _ = ∫ o in U, M.pi (W o) ∂M.law :=
        integral_eval_preimage M hM.probability n i t ht (fun o => M.pi (W o))
          (unit_pi_integrable M hM)
      _ = ∫ o in U, X o ∂M.law := hsingle.symm
      _ = ∫ a in {a : Sample n | W (a i) ∈ t}, X (a i) ∂μ := by
        symm
        exact integral_eval_preimage M hM.probability n i t ht X (unit_X_integrable M hM)
      _ = ∫ a in s, x a ∂μ := by
        change (∫ a in (fun a : Sample n => W (a i)) ⁻¹' t, X (a i) ∂μ) =
          ∫ a in s, X (a i) ∂μ
        rw [← hseq]
  · exact hqsm.aestronglyMeasurable

end
end SAP.P046.WH.W2.P.T8_L4

open MeasureTheory ProbabilityTheory

theorem SAP.P046.WH.W2.T8_L4_proof : SAP.P046.WH.W2.T8_L4 := by
  intro M hM n F i hind
  intro hpred
  letI : IsProbabilityMeasure M.law := hM.probability
  let μ := sampleLaw M n
  let x : Sample n → ℝ := fun a => X (a i)
  let G : Sample n → ℝ := wholePrediction F i
  let r : Sample n → ℝ := fun a => (M.pi (W (a i)))⁻¹
  have hle : wholeOwnSigma n i ≤ (inferInstance : MeasurableSpace (Sample n)) :=
    (measurable_fst.comp (measurable_pi_apply i)).comap_le
  have hXmeas : Measurable x := by
    change Measurable (fun a : Sample n => X (a i))
    exact (measurable_of_countable bit).comp
      (measurable_snd.fst.comp (measurable_pi_apply i))
  have hGmeas : Measurable G := by
    change Measurable (wholePrediction F i)
    exact (F.measurable_g _).comp (measurable_id.prodMk
      (measurable_fst.comp (measurable_pi_apply i)))
  have hxrange (a : Sample n) : x a ∈ Set.Icc (0 : ℝ) 1 := by
    change 0 ≤ x a ∧ x a ≤ 1
    cases hz : (a i).2.1 <;> simp [x, X, bit, hz]
  have hxnorm (a : Sample n) : ‖x a‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hxrange a).1]
    exact (hxrange a).2
  have hp : MeasurePreserving (fun a : Sample n => a i) μ M.law :=
    measurePreserving_eval (fun _ : Fin n => M.law) i
  have hxint : Integrable x μ := by
    exact hp.integrable_comp_of_integrable
      (SAP.P046.WH.W2.P.T8_L4.unit_X_integrable M hM)
  have hprodint : Integrable (fun a => x a * G a) μ := by
    exact hpred.bdd_mul hXmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => hxnorm a)
  change CondIndepFun (wholeOwnSigma n i)
    (by exact (measurable_fst.comp (measurable_pi_apply i)).comap_le)
    (fun a => X (a i)) (wholePrediction F i) (sampleLaw M n) at hind
  have hfactor := SAP.P046.WH.W2.P.T8_L4.condExp_mul_of_condIndep hle x G hXmeas hGmeas
    hprodint hxint hpred hind
  have hprop := SAP.P046.WH.W2.P.T8_L4.eval_propensity M hM n i
  have hpos : ∀ᵐ a ∂μ, M.delta < M.pi (W (a i)) ∧
      M.pi (W (a i)) < 1 - M.delta :=
    hp.quasiMeasurePreserving.ae hM.positivity
  have hrange : ∀ᵐ a ∂μ, ‖(fun a => x a / M.pi (W (a i))) a‖ ≤ M.delta⁻¹ := by
    filter_upwards [hpos] with a ha
    have hden : 0 < M.pi (W (a i)) := hM.delta_pos.trans ha.1
    have hinv : (M.pi (W (a i)))⁻¹ ≤ M.delta⁻¹ :=
      (inv_le_inv₀ hden hM.delta_pos).2 ha.1.le
    have hx0 := (hxrange a).1
    have hx1 := (hxrange a).2
    have hq0 : 0 ≤ x a / M.pi (W (a i)) := div_nonneg hx0 hden.le
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    calc
      x a / M.pi (W (a i)) = x a * (M.pi (W (a i)))⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 1 * M.delta⁻¹ := mul_le_mul hx1 hinv (inv_nonneg.mpr hden.le) (by positivity)
      _ = M.delta⁻¹ := by simp
  have hqmeas : Measurable (fun a : Sample n => x a / M.pi (W (a i))) := by
    exact hXmeas.div (hM.measurable_pi.comp
      (measurable_fst.comp (measurable_pi_apply i)))
  have hweightedInt : Integrable (wholeWeightedPrediction M F i) μ := by
    have hmul := hpred.bdd_mul hqmeas.aestronglyMeasurable hrange
    have heq : (fun a => (x a / M.pi (W (a i))) * G a) =
        wholeWeightedPrediction M F i := by
      funext a
      simp [x, G, wholePrediction, wholeWeightedPrediction, div_eq_mul_inv]
      ring
    rw [← heq]
    exact hmul
  have hrsm : StronglyMeasurable[wholeOwnSigma n i] r := by
    letI : MeasurableSpace (Sample n) := wholeOwnSigma n i
    have hpi : Measurable[wholeOwnSigma n i] (fun a : Sample n => M.pi (W (a i))) :=
      hM.measurable_pi.comp (comap_measurable (fun a : Sample n => W (a i)))
    exact hpi.inv.stronglyMeasurable
  have hprodWeight : (fun a => wholeWeightedPrediction M F i a) =
      (fun a => r a * (x a * G a)) := by
    funext a
    simp [r, x, G, wholeWeightedPrediction, wholePrediction, div_eq_mul_inv]
    ring
  have hprodWeightInt : Integrable (fun a => r a * (x a * G a)) μ := by
    rw [← hprodWeight]
    exact hweightedInt
  have hpull₀ := condExp_mul_of_stronglyMeasurable_left hrsm hprodWeightInt hprodint
  have hpull : condExp (wholeOwnSigma n i) μ (wholeWeightedPrediction M F i) =ᵐ[μ]
      fun a => r a * condExp (wholeOwnSigma n i) μ (fun b => x b * G b) a := by
    exact (condExp_congr_ae (Filter.Eventually.of_forall fun a => congrFun hprodWeight a)).trans hpull₀
  have hcond : condExp (wholeOwnSigma n i) μ (wholeWeightedPrediction M F i) =ᵐ[μ]
      fun a => condExp (wholeOwnSigma n i) μ (fun b => x b) a *
        condExp (wholeOwnSigma n i) μ G a / M.pi (W (a i)) := by
    filter_upwards [hpull, hfactor] with a hp hf
    rw [hp, hf]
    simp [r, div_eq_mul_inv]
    ring
  have hceWeightedInt : Integrable
      (condExp (wholeOwnSigma n i) μ (wholeWeightedPrediction M F i)) μ := integrable_condExp
  have hcondInt : Integrable (fun a =>
      condExp (wholeOwnSigma n i) μ (fun b => x b) a *
        condExp (wholeOwnSigma n i) μ G a / M.pi (W (a i))) μ :=
    hceWeightedInt.congr hcond
  have hceGInt : Integrable (condExp (wholeOwnSigma n i) μ G) μ := integrable_condExp
  have hcancel : (fun a =>
      condExp (wholeOwnSigma n i) μ (fun b => x b) a *
        condExp (wholeOwnSigma n i) μ G a / M.pi (W (a i))) =ᵐ[μ]
      condExp (wholeOwnSigma n i) μ G := by
    filter_upwards [hprop, hpos] with a hpa hba
    rw [hpa]
    exact mul_div_cancel_left₀ _ (ne_of_gt (hM.delta_pos.trans hba.1))
  refine ⟨hweightedInt, ?_, ?_, ?_⟩
  · simpa [x, G, μ] using hfactor
  · calc
      (∫ a, wholeWeightedPrediction M F i a ∂μ) =
          ∫ a, condExp (wholeOwnSigma n i) μ (wholeWeightedPrediction M F i) a ∂μ :=
        (integral_condExp hle).symm
      _ = ∫ a, condExp (wholeOwnSigma n i) μ (fun b => x b) a *
            condExp (wholeOwnSigma n i) μ G a / M.pi (W (a i)) ∂μ :=
        integral_congr_ae hcond
  · calc
      (∫ a, condExp (wholeOwnSigma n i) μ (fun b => x b) a *
            condExp (wholeOwnSigma n i) μ G a / M.pi (W (a i)) ∂μ) =
          ∫ a, condExp (wholeOwnSigma n i) μ G a ∂μ := integral_congr_ae hcancel
      _ = ∫ a, wholePrediction F i a ∂μ := integral_condExp hle
