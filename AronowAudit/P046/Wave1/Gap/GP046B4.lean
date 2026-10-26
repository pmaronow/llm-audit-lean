import AronowAudit.P046.P046_Audit

namespace AronowAudit.P046.Wave1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal
noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

lemma zero_benchmark_q_bounds (M : Study) (hM : ValidStudy M) :
    ∀ᵐ o ∂M.law, 0 ≤ q M (W o) ∧ |q M (W o)| ≤ M.delta⁻¹ := by
  filter_upwards [hM.positivity] with o ho
  have hp : 0 < M.pi (W o) := lt_trans hM.delta_pos ho.1
  have hnum : 0 ≤ 1 - M.pi (W o) := by linarith [hM.delta_pos]
  have hq : 0 ≤ q M (W o) := div_nonneg hnum hp.le
  refine ⟨hq, ?_⟩
  rw [abs_of_nonneg hq]
  unfold q
  calc
    (1 - M.pi (W o)) / M.pi (W o) ≤ 1 / M.pi (W o) := by
      gcongr
      linarith
    _ ≤ M.delta⁻¹ := by simpa only [one_div] using (inv_le_inv₀ hp hM.delta_pos).2 ho.1.le

lemma zero_benchmark_weighted_integrable (M : Study) (hM : ValidStudy M)
    (f : Unit → ℝ) (hf : MemLp f 2 M.law) :
    Integrable (fun o => q M (W o) * (f o)^2) M.law := by
  apply hf.integrable_sq.bdd_mul
  · exact (((measurable_const.sub (hM.measurable_pi.comp measurable_fst)).div
      (hM.measurable_pi.comp measurable_fst))).aestronglyMeasurable
  · exact (zero_benchmark_q_bounds M hM).mono fun o ho => by simpa only [Real.norm_eq_abs] using ho.2

lemma zero_benchmark_y1_L2 (M : Study) (hM : ValidStudy M) : MemLp Y1 2 M.law := by
  letI := hM.probability
  have hy : Measurable Y1 := (measurable_of_countable bit).comp measurable_snd.snd.snd
  apply memLp_of_bounded (a := 0) (b := 1) _ hy.aestronglyMeasurable 2
  exact Filter.Eventually.of_forall fun o => by
    rcases o with ⟨w, x, y0, y1⟩
    cases y1 <;> norm_num [Y1, bit]

lemma zero_benchmark_young (M : Study) (hM : ValidStudy M)
    (g : ℝ → ℝ) (hg : MemLp (fun o => g (W o)) 2 M.law)
    (t : ℝ) (ht : 0 < t) :
    risk M g ≤ (1 + t) * risk M (fun _ => 0) + (1 + t⁻¹) * weightedNormSq M g := by
  have hy := zero_benchmark_y1_L2 M hM
  have hi := zero_benchmark_weighted_integrable M hM _ (hy.sub hg)
  have h0 := zero_benchmark_weighted_integrable M hM _ hy
  have hg' := zero_benchmark_weighted_integrable M hM _ hg
  have hineq : ∀ᵐ o ∂M.law,
      q M (W o) * (Y1 o - g (W o))^2 ≤
        (1 + t) * (q M (W o) * (Y1 o)^2) +
        (1 + t⁻¹) * (q M (W o) * (g (W o))^2) := by
    filter_upwards [zero_benchmark_q_bounds M hM] with o ho
    have hs := sq_nonneg (t * Y1 o + g (W o))
    have hi : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    have hu : (Y1 o - g (W o))^2 ≤ (1 + t) * (Y1 o)^2 +
        (1 + t⁻¹) * (g (W o))^2 := by
      apply (mul_le_mul_iff_right₀ ht).mp
      have hid : t * ((1+t) * (Y1 o)^2 + (1+t⁻¹) * (g (W o))^2) -
          t * (Y1 o - g (W o))^2 = (t * Y1 o + g (W o))^2 := by
        field_simp [ht.ne'] <;> ring
      nlinarith only [hs, hid]
    convert mul_le_mul_of_nonneg_left hu ho.1 using 1 <;> ring
  have h := integral_mono_ae hi ((h0.const_mul (1+t)).add (hg'.const_mul (1+t⁻¹))) hineq
  simp only [Pi.add_apply, Pi.sub_apply] at h
  rw [integral_add (h0.const_mul _) (hg'.const_mul _), integral_const_mul,
    integral_const_mul] at h
  simpa only [risk, weightedNormSq, sub_zero] using h

 theorem zero_benchmark_risk_proof (M : Study) (hM : ValidStudy M) (G : Set (ℝ → ℝ))
    (hG : ∀ g ∈ G, MemLp (fun o => g (W o)) 2 M.law)
    (hzero : ZeroBenchmark M G) (gstar : ℝ → ℝ) (hstar : gstar ∈ G)
    (hmin : ∀ g ∈ G, risk M gstar ≤ risk M g) : risk M gstar ≤ risk M (fun _ => 0) := by
  rcases hzero with hz | ⟨h, hh, hlim⟩
  · exact hmin _ hz
  have hbound : ∀ t : ℝ, 0 < t → risk M gstar ≤ (1+t) * risk M (fun _ => 0) := by
    intro t ht
    have hl : Tendsto (fun k => (1+t) * risk M (fun _ => 0) +
        (1+t⁻¹) * weightedNormSq M (h k)) atTop
        (nhds ((1+t) * risk M (fun _ => 0))) := by
      simpa using tendsto_const_nhds.add (hlim.const_mul (1+t⁻¹))
    exact ge_of_tendsto' hl fun k => (hmin _ (hh k)).trans
      (zero_benchmark_young M hM (h k) (hG _ (hh k)) t ht)
  have hl : Tendsto (fun k : ℕ => (1 + 1 / ((k : ℝ) + 1)) * risk M (fun _ => 0))
      atTop (nhds (risk M (fun _ => 0))) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat).mul_const
      (risk M (fun _ => 0))
  exact ge_of_tendsto' hl fun k => hbound _ (by positivity)

lemma proposition4a_multiplier_measurable (M : Study) (hM : ValidStudy M) :
    Measurable (fun o => 1 - X o / M.pi (W o)) :=
  measurable_const.sub (((measurable_of_countable bit).comp measurable_snd.fst).div
    (hM.measurable_pi.comp measurable_fst))

lemma proposition4a_multiplier_bound (M : Study) (hM : ValidStudy M) :
    ∀ᵐ o ∂M.law, ‖1 - X o / M.pi (W o)‖ ≤ 1 + M.delta⁻¹ := by
  filter_upwards [hM.positivity] with o ho
  have hp : 0 < M.pi (W o) := lt_trans hM.delta_pos ho.1
  have hb : (M.pi (W o))⁻¹ ≤ M.delta⁻¹ := (inv_le_inv₀ hp hM.delta_pos).2 ho.1.le
  have hx : |X o| ≤ 1 := by
    rcases o with ⟨w, x, y0, y1⟩
    cases x <;> norm_num [X, bit]
  rw [Real.norm_eq_abs]
  calc
    |1 - X o / M.pi (W o)| ≤ |(1 : ℝ)| + |X o / M.pi (W o)| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (1 : ℝ) (-(X o / M.pi (W o)))
    _ ≤ 1 + M.delta⁻¹ := by
      rw [abs_one, abs_div, abs_of_pos hp]
      gcongr
      calc
        |X o| / M.pi (W o) ≤ 1 / M.pi (W o) := div_le_div_of_nonneg_right hx hp.le
        _ ≤ M.delta⁻¹ := by simpa only [one_div] using hb

lemma proposition4a_multiplier_cancel (M : Study) (hM : ValidStudy M)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable (fun o => f (W o)) M.law) :
    (∫ o, (1 - X o / M.pi (W o)) * f (W o) ∂M.law) = 0 := by
  letI := hM.probability
  have hm : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  letI : IsFiniteMeasure (M.law.trim hm) := isFiniteMeasure_trim hm
  have mx : Measurable X := (measurable_of_countable bit).comp measurable_snd.fst
  have ix : Integrable X M.law := by
    apply memLp_one_iff_integrable.mp
    apply memLp_of_bounded (a := 0) (b := 1) _ mx.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun o => by
      rcases o with ⟨w, x, y0, y1⟩
      cases x <;> norm_num [X, bit]
  have ip : Integrable (fun o => (1 - X o / M.pi (W o)) * f (W o)) M.law :=
    hi.bdd_mul (proposition4a_multiplier_measurable M hM).aestronglyMeasurable
      (proposition4a_multiplier_bound M hM)
  have isub := hi.sub ip
  have ixprod : Integrable (fun o => (f (W o) / M.pi (W o)) * X o) M.law := by
    convert isub using 1
    ext o
    dsimp
    ring
  have mfp : StronglyMeasurable[covariateSigma] (fun o => f (W o) / M.pi (W o)) :=
    ((hf.comp (comap_measurable W)).div
      (hM.measurable_pi.comp (comap_measurable W))).stronglyMeasurable
  have hpull := condExp_mul_of_stronglyMeasurable_left mfp ixprod ix
  have hc : condExp covariateSigma M.law (fun o => f (W o) / M.pi (W o) * X o)
      =ᵐ[M.law] fun o => f (W o) := by
    filter_upwards [hpull, hM.propensity, hM.positivity] with o h1 h2 ho
    change condExp covariateSigma M.law (fun o => f (W o) / M.pi (W o) * X o) o =
      (f (W o) / M.pi (W o)) * condExp covariateSigma M.law X o at h1
    rw [h1, h2, div_mul_cancel₀ _ (ne_of_gt (lt_trans hM.delta_pos ho.1))]
  have he : (∫ o, (f (W o) / M.pi (W o)) * X o ∂M.law) = ∫ o, f (W o) ∂M.law := by
    rw [← integral_condExp hm (f := fun o => (f (W o) / M.pi (W o)) * X o)]
    exact integral_congr_ae hc
  calc
    _ = ∫ o, f (W o) - (f (W o) / M.pi (W o)) * X o ∂M.law := by
      congr 1
      ext o
      ring
    _ = 0 := by rw [integral_sub hi ixprod, he, sub_self]

lemma proposition4a_fit_insert {n : ℕ} (F : CrossFit (n+1)) (i : Fin (n+1))
    (a : Fin n → Unit) (o o' : Unit) :
    F.g (F.fold i) (i.insertNth o a) = F.g (F.fold i) (i.insertNth o' a) := by
  apply F.opposite_fold
  intro k hk
  have hki : k ≠ i := by rintro rfl; exact hk rfl
  obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hki
  simp

lemma proposition4a_augmentation (M : Study) (hM : ValidStudy M) (n : ℕ)
    (F : CrossFit n) (i : Fin n)
    (hint : Integrable (fun a => F.g (F.fold i) a (W (a i))) (sampleLaw M n)) :
    Integrable (fun a => (1-X (a i)/M.pi (W (a i))) * F.g (F.fold i) a (W (a i)))
      (sampleLaw M n) ∧
    (∫ a, (1-X (a i)/M.pi (W (a i))) * F.g (F.fold i) a (W (a i))
      ∂sampleLaw M n) = 0 := by
  letI := hM.probability
  have hp := measurePreserving_eval (fun _ : Fin n => M.law) i
  have hi : Integrable (fun a => (1-X (a i)/M.pi (W (a i))) * F.g (F.fold i) a (W (a i)))
      (sampleLaw M n) := by
    apply hint.bdd_mul
    · exact (proposition4a_multiplier_measurable M hM).aestronglyMeasurable.comp_measurePreserving hp
    · exact hp.quasiMeasurePreserving.ae (proposition4a_multiplier_bound M hM)
  refine ⟨hi, ?_⟩
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Unit) i
    have hpres := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => M.law) i).symm
    have hhint := hpres.integrable_comp_of_integrable hint
    have hhi := hpres.integrable_comp_of_integrable hi
    have hsec := hhint.prod_left_ae
    have hz : ∀ᵐ a ∂sampleLaw M n,
        (∫ o, (1-X o/M.pi (W o)) * F.g (F.fold i) (i.insertNth o a) (W o) ∂M.law) = 0 := by
      filter_upwards [hsec] with a ha
      let o0 : Unit := (0, (false, (false, false)))
      have hm : Measurable (F.g (F.fold i) (i.insertNth o0 a)) :=
        (F.measurable_g _).comp (measurable_const.prodMk measurable_id)
      have hfit : ∀ o, F.g (F.fold i) (i.insertNth o a) = F.g (F.fold i) (i.insertNth o0 a) :=
        fun o => proposition4a_fit_insert F i a o o0
      have hai : Integrable (fun o => F.g (F.fold i) (i.insertNth o0 a) (W o)) M.law := by
        simpa only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Function.comp_def, Fin.insertNth_apply_same, hfit] using ha
      simp_rw [hfit]
      exact proposition4a_multiplier_cancel M hM _ hm hai
    calc
      _ = ∫ z : Unit × Sample n,
          (1-X (e.symm z i)/M.pi (W (e.symm z i))) *
            F.g (F.fold i) (e.symm z) (W (e.symm z i))
          ∂M.law.prod (sampleLaw M n) := (hpres.integral_comp' _).symm
      _ = ∫ a, ∫ o, (1-X o/M.pi (W o)) *
          F.g (F.fold i) (i.insertNth o a) (W o) ∂M.law ∂sampleLaw M n := by
        convert integral_prod_symm _ hhi using 1 <;>
          simp only [sampleLaw, Function.comp_def, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same]
      _ = 0 := by rw [integral_congr_ae hz, integral_zero]

 theorem proposition4a_proof (M : Study) (hM : ValidStudy M) (n : ℕ) (hn : 0 < n)
    (F : CrossFit n)
    (hint : ∀ i, Integrable (fun a => F.g (F.fold i) a (W (a i))) (sampleLaw M n)) :
    (∫ a, adjusted M F a ∂sampleLaw M n) = mu M := by
  letI := hM.probability
  have hh : ∀ i : Fin n, Integrable (fun a => htTerm (M.pi (W (a i))) (X (a i)) (Y (a i)))
      (sampleLaw M n) := fun i => (measurePreserving_eval (fun _ : Fin n => M.law) i).integrable_comp_of_integrable (ht_unit_facts M hM).1
  have hi := fun i => proposition4a_augmentation M hM n F i (hint i)
  have hpoint : adjusted M F = fun a => ht M a +
      (∑ i, (1-X (a i)/M.pi (W (a i))) * F.g (F.fold i) a (W (a i))) / n := by
    funext a
    simp only [adjusted, adjusted_decomposition, Finset.sum_add_distrib, add_div, ht]
  have iht : Integrable (ht M (n := n)) (sampleLaw M n) :=
    (integrable_finset_sum _ (fun i _ => hh i)).div_const _
  have iaug : Integrable (fun a => ∑ i, (1-X (a i)/M.pi (W (a i))) *
      F.g (F.fold i) a (W (a i))) (sampleLaw M n) :=
    integrable_finset_sum _ (fun i _ => (hi i).1)
  rw [hpoint, integral_add iht (iaug.div_const _), ht_unbiased M hM n hn, integral_div]
  have hs := integral_finsetSum Finset.univ (fun i _ => (hi i).1)
  rw [hs]
  simp only [(hi _).2, Finset.sum_const_zero, zero_div, add_zero]

lemma proposition4b_sum_sq {ι : Type*} [Fintype ι] (M : Study) (hM : ValidStudy M)
    (f : Unit → ℝ) (hf : MemLp f 2 M.law) (hz : (∫ o, f o ∂M.law) = 0) :
    (∫ a : ι → Unit, (∑ i, f (a i))^2 ∂Measure.pi (fun _ => M.law)) =
      Fintype.card ι * (∫ o, (f o)^2 ∂M.law) := by
  letI := hM.probability
  have hsum : MemLp (fun a : ι → Unit => ∑ i, f (a i)) 2 (Measure.pi (fun _ => M.law)) :=
    memLp_finsetSum _ (fun i _ => hf.comp_measurePreserving (measurePreserving_eval _ i))
  have he : (∫ a : ι → Unit, (∑ i, f (a i)) ∂Measure.pi (fun _ => M.law)) = 0 := by
    have hsi := integral_finsetSum Finset.univ (fun i _ =>
      (hf.comp_measurePreserving (measurePreserving_eval (fun _ : ι => M.law) i)).integrable (by norm_num))
    change (∫ a : ι → Unit, ∑ i, f (a i) ∂Measure.pi (fun _ => M.law)) = _ at hsi
    rw [hsi]
    have hei : ∀ i : ι, (∫ a : ι → Unit, f (a i) ∂Measure.pi (fun _ => M.law)) =
        ∫ o, f o ∂M.law := fun i => integral_comp_eval (μ := fun _ : ι => M.law) (i := i) hf.aestronglyMeasurable
    simp only [Function.comp_def, Function.eval, hei, hz, Finset.sum_const_zero]
  calc
    _ = variance (fun a : ι → Unit => ∑ i, f (a i)) (Measure.pi (fun _ => M.law)) := by
      rw [variance_eq_integral hsum.aemeasurable, he]
      simp only [sub_zero]
    _ = Fintype.card ι * variance f M.law := by
      convert variance_sum_pi (fun _ : ι => hf) using 1
      · simp only [Finset.sum_fn]
      · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := by rw [variance_eq_integral hf.aemeasurable, hz]; simp only [sub_zero]

lemma proposition4b_multiplier_L2 (M : Study) (hM : ValidStudy M) (f : ℝ → ℝ)
    (hf : MemLp (fun o => f (W o)) 2 M.law) :
    MemLp (fun o => (1-X o/M.pi (W o)) * f (W o)) 2 M.law := by
  apply hf.of_le_mul ((proposition4a_multiplier_measurable M hM).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [proposition4a_multiplier_bound M hM] with o ho
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right ho (norm_nonneg _)

lemma proposition4b_fit_norm_measurable (M : Study) (hM : ValidStudy M) (n : ℕ) (F : CrossFit n) (j : Bool) :
    Measurable (fun a => l2Sq M (F.g j a)) := by
  letI := hM.probability
  have h : Measurable (fun z : Sample n × Unit => (F.g j z.1 (W z.2))^2) :=
    ((F.measurable_g j).comp (measurable_fst.prodMk measurable_snd.fst)).pow_const 2
  exact h.stronglyMeasurable.integral_prod_right'.measurable

lemma proposition4b_fit_norm_integrable (M : Study) (hM : ValidStudy M) (n : ℕ)
    (F : CrossFit n) (j : Bool) (g : ℝ → ℝ)
    (hg : MemLp (fun o => g (W o)) 2 M.law)
    (hfits : ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => F.g j a (W o)) 2 M.law)
    (hi : Integrable (fun a => l2Sq M (fun w => F.g j a w - g w)) (sampleLaw M n)) :
    Integrable (fun a => l2Sq M (F.g j a)) (sampleLaw M n) ∧
    (∫ a, l2Sq M (F.g j a) ∂sampleLaw M n) ≤
      2 * (∫ a, l2Sq M (fun w => F.g j a w - g w) ∂sampleLaw M n) + 2 * l2Sq M g := by
  letI := hM.probability
  have hb : ∀ᵐ a ∂sampleLaw M n, l2Sq M (F.g j a) ≤
      2 * l2Sq M (fun w => F.g j a w - g w) + 2 * l2Sq M g := by
    filter_upwards [hfits] with a ha
    have ht := integral_mono ha.integrable_sq
      (((ha.sub hg).integrable_sq.const_mul 2).add (hg.integrable_sq.const_mul 2))
      (fun o => by dsimp; nlinarith [sq_nonneg (F.g j a (W o) - 2 * g (W o))])
    simp only [Pi.add_apply, Pi.sub_apply] at ht
    have idiff : Integrable (fun o => 2 * (F.g j a (W o) - g (W o))^2) M.law :=
      (ha.sub hg).integrable_sq.const_mul 2
    have ig : Integrable (fun o => 2 * (g (W o))^2) M.law := hg.integrable_sq.const_mul 2
    rw [integral_add idiff ig, integral_const_mul, integral_const_mul] at ht
    exact ht
  have hi' : Integrable (fun a => 2 * l2Sq M (fun w => F.g j a w - g w) +
      2 * l2Sq M g) (sampleLaw M n) := (hi.const_mul 2).add (integrable_const _)
  have hh : Integrable (fun a => l2Sq M (F.g j a)) (sampleLaw M n) := by
    apply hi'.mono' (proposition4b_fit_norm_measurable M hM n F j).aestronglyMeasurable
    filter_upwards [hb] with a ha
    have hnn : 0 ≤ l2Sq M (F.g j a) := integral_nonneg (fun o => sq_nonneg (F.g j a (W o)))
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using ha
  refine ⟨hh, ?_⟩
  have ht := integral_mono_ae hh hi' hb
  simpa only [integral_add (hi.const_mul 2) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul] using ht


lemma proposition4b_fold_sum_bound (M : Study) (hM : ValidStudy M) (n : ℕ)
    (F : CrossFit n) (j : Bool)
    (hfits : ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => F.g j a (W o)) 2 M.law)
    (hnorm : Integrable (fun a => l2Sq M (F.g j a)) (sampleLaw M n)) :
    Integrable (fun a => (∑ i : {i : Fin n // F.fold i = j},
      (1-X (a i)/M.pi (W (a i))) * F.g j a (W (a i)))^2) (sampleLaw M n) ∧
    (∫ a, (∑ i : {i : Fin n // F.fold i = j},
      (1-X (a i)/M.pi (W (a i))) * F.g j a (W (a i)))^2 ∂sampleLaw M n) ≤
      Fintype.card {i : Fin n // F.fold i = j} * (1+M.delta⁻¹)^2 *
        (∫ a, l2Sq M (F.g j a) ∂sampleLaw M n) := by
  classical
  letI := hM.probability
  let E := {i : Fin n // F.fold i = j}
  let T := {i : Fin n // ¬ F.fold i = j}
  let νE : Measure (E → Unit) := Measure.pi (fun _ => M.law)
  let νT : Measure (T → Unit) := Measure.pi (fun _ => M.law)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Unit) (fun i => F.fold i = j)
  have hp : MeasurePreserving e.symm (νE.prod νT) (sampleLaw M n) :=
    (measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => M.law) (fun i => F.fold i = j)).symm
  let base : (T → Unit) → Sample n := fun t => e.symm ((fun _ => (0, (false, (false, false)))), t)
  have mb : Measurable base := e.symm.measurable.comp (measurable_const.prodMk measurable_id)
  have hfit : ∀ (x : E → Unit) (t : T → Unit), F.g j (e.symm (x,t)) = F.g j (base t) := by
    intro x t
    apply F.opposite_fold
    intro i hi
    simp [e, base, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
  have heval : ∀ (x : E → Unit) (t : T → Unit) (i : E), e.symm (x,t) i = x i := by
    intro x t i
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, i.property]
  have htfit : ∀ᵐ t ∂νT, MemLp (fun o => F.g j (base t) (W o)) 2 M.law := by
    obtain ⟨x, hx⟩ := (Measure.ae_ae_of_ae_prod (hp.quasiMeasurePreserving.ae hfits)).exists
    filter_upwards [hx] with t ht
    change MemLp (fun o => F.g j (e.symm (x,t)) (W o)) 2 M.law at ht
    simpa only [hfit] using ht
  have hnp := hp.integrable_comp_of_integrable hnorm
  have hnt : Integrable (fun t => l2Sq M (F.g j (base t))) νT := by
    have h := hnp.integral_prod_right
    simpa only [Function.comp_def, hfit, integral_const, probReal_univ, one_smul] using h
  have hn_eq : (∫ a, l2Sq M (F.g j a) ∂sampleLaw M n) =
      ∫ t, l2Sq M (F.g j (base t)) ∂νT := by
    rw [← hp.integral_comp' _]
    trans ∫ t, ∫ x, ((fun a => l2Sq M (F.g j a)) ∘ e.symm) (x,t) ∂νE ∂νT
    · exact integral_prod_symm _ hnp
    · simp only [Function.comp_def, hfit, integral_const, probReal_univ, one_smul]
  let S : (E → Unit) × (T → Unit) → ℝ := fun z =>
    ∑ i : E, (1-X (z.1 i)/M.pi (W (z.1 i))) * F.g j (base z.2) (W (z.1 i))
  have mS : Measurable S := by
    apply Finset.measurable_sum
    intro i hi
    exact ((proposition4a_multiplier_measurable M hM).comp
      ((measurable_pi_apply i).comp measurable_fst)).mul
      ((F.measurable_g j).comp ((mb.comp measurable_snd).prodMk
        (measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst))))
  have hsections : ∀ᵐ t ∂νT,
      Integrable (fun x => (S (x,t))^2) νE ∧
      (∫ x, (S (x,t))^2 ∂νE) ≤ Fintype.card E * (1+M.delta⁻¹)^2 * l2Sq M (F.g j (base t)) := by
    filter_upwards [htfit] with t ht
    let f : Unit → ℝ := fun o => (1-X o/M.pi (W o)) * F.g j (base t) (W o)
    have hf := proposition4b_multiplier_L2 M hM (F.g j (base t)) ht
    have hf0 := proposition4a_multiplier_cancel M hM (F.g j (base t))
      ((F.measurable_g j).comp (measurable_const.prodMk measurable_id)) (ht.integrable (by norm_num))
    have hs : MemLp (fun x : E → Unit => ∑ i, f (x i)) 2 νE :=
      memLp_finsetSum _ (fun i _ => hf.comp_measurePreserving (measurePreserving_eval _ i))
    refine ⟨hs.integrable_sq, ?_⟩
    have hunit : (∫ o, (f o)^2 ∂M.law) ≤ (1+M.delta⁻¹)^2 * l2Sq M (F.g j (base t)) := by
      have h := integral_mono_ae hf.integrable_sq (ht.integrable_sq.const_mul ((1+M.delta⁻¹)^2)) ?_
      · simpa only [integral_const_mul, l2Sq] using h
      filter_upwards [proposition4a_multiplier_bound M hM] with o ho
      have hd : (1-X o/M.pi (W o))^2 ≤ (1+M.delta⁻¹)^2 := by
        rw [Real.norm_eq_abs] at ho
        have hh : 0 ≤ 1+M.delta⁻¹ := add_nonneg zero_le_one (inv_nonneg.mpr hM.delta_pos.le)
        have hsq := (sq_le_sq₀ (abs_nonneg (1-X o/M.pi (W o))) hh).2 ho
        simpa only [sq_abs] using hsq
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hd (sq_nonneg _)
    change (∫ x : E → Unit, (∑ i, f (x i))^2 ∂νE) ≤ _
    rw [proposition4b_sum_sq M hM f hf hf0]
    have hh := mul_le_mul_of_nonneg_left hunit (Nat.cast_nonneg (α := ℝ) (Fintype.card E))
    convert hh using 1 <;> ring
  have hprod : Integrable (fun z => (S z)^2) (νE.prod νT) := by
    apply (integrable_prod_iff' (mS.pow_const 2).aestronglyMeasurable).2
    refine ⟨hsections.mono fun t ht => ht.1, ?_⟩
    have hdom := hnt.const_mul (Fintype.card E * (1+M.delta⁻¹)^2)
    simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    apply hdom.mono' ((mS.pow_const 2).stronglyMeasurable.integral_prod_left').aestronglyMeasurable
    filter_upwards [hsections] with t ht
    have hnn : 0 ≤ ∫ x, (S (x,t))^2 ∂νE := integral_nonneg (fun x => sq_nonneg (S (x,t)))
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using ht.2
  have hS : (fun z => ∑ i : E, (1-X (e.symm z i)/M.pi (W (e.symm z i))) *
      F.g j (e.symm z) (W (e.symm z i))) = S := by
    funext z
    rcases z with ⟨x,t⟩
    simp only [heval, hfit, S]
  have hi : Integrable (fun a => (∑ i : E, (1-X (a i)/M.pi (W (a i))) *
      F.g j a (W (a i)))^2) (sampleLaw M n) := by
    apply (hp.integrable_comp_emb e.symm.measurableEmbedding).mp
    exact hprod.congr (Filter.Eventually.of_forall fun z =>
      (congrArg (fun r : ℝ => r^2) (congrFun hS z)).symm)
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ z, (S z)^2 ∂νE.prod νT := by
      rw [← hp.integral_comp' _]
      congr 1
      funext z
      exact congrArg (fun r : ℝ => r^2) (congrFun hS z)
    _ = ∫ t, ∫ x, (S (x,t))^2 ∂νE ∂νT := integral_prod_symm _ hprod
    _ ≤ ∫ t, (Fintype.card E * (1+M.delta⁻¹)^2) * l2Sq M (F.g j (base t)) ∂νT :=
      integral_mono_ae hprod.integral_prod_right
        (hnt.const_mul (Fintype.card E * (1+M.delta⁻¹)^2)) (hsections.mono fun t ht => ht.2)
    _ = _ := by rw [integral_const_mul, ← hn_eq]


lemma proposition4b_fold_scaled_bound (M : Study) (hM : ValidStudy M) (n : ℕ) (hn : 0 < n)
    (F : CrossFit n) (j : Bool)
    (hfits : ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => F.g j a (W o)) 2 M.law)
    (hnorm : Integrable (fun a => l2Sq M (F.g j a)) (sampleLaw M n)) :
    Integrable (fun a => (Real.sqrt n * foldRemainder M F j (fun _ => 0) a)^2) (sampleLaw M n) ∧
    (∫ a, (Real.sqrt n * foldRemainder M F j (fun _ => 0) a)^2 ∂sampleLaw M n) ≤
      (1+M.delta⁻¹)^2 * (∫ a, l2Sq M (F.g j a) ∂sampleLaw M n) := by
  classical
  letI := hM.probability
  let E := {i : Fin n // F.fold i = j}
  let S : Sample n → ℝ := fun a => ∑ i : E,
    (1-X (a i)/M.pi (W (a i))) * F.g j a (W (a i))
  have he : ∀ a, foldRemainder M F j (fun _ => 0) a = S a / n := by
    intro a
    simp only [foldRemainder, sub_zero, S]
    congr 1
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  have hsq : ∀ a, (Real.sqrt n * foldRemainder M F j (fun _ => 0) a)^2 =
      (n : ℝ)⁻¹ * (S a)^2 := by
    intro a
    rw [he, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), div_pow]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hn'] <;> ring
  have hb := proposition4b_fold_sum_bound M hM n F j hfits hnorm
  refine ⟨?_, ?_⟩
  · simpa only [hsq] using hb.1.const_mul (n : ℝ)⁻¹
  rw [show (fun a => (Real.sqrt n * foldRemainder M F j (fun _ => 0) a)^2) =
    (fun a => (n : ℝ)⁻¹ * (S a)^2) from funext hsq, integral_const_mul]
  have hcard : (Fintype.card E : ℝ) ≤ n := by
    have hc : Fintype.card E ≤ n := by
      simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin n => F.fold i = j)
    exact_mod_cast hc
  have hnonneg : 0 ≤ (1+M.delta⁻¹)^2 * (∫ a, l2Sq M (F.g j a) ∂sampleLaw M n) := by
    apply mul_nonneg (sq_nonneg _)
    exact integral_nonneg fun a => integral_nonneg fun o => sq_nonneg _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (n : ℝ)⁻¹ * (Fintype.card E * (1+M.delta⁻¹)^2 *
        (∫ a, l2Sq M (F.g j a) ∂sampleLaw M n)) :=
      mul_le_mul_of_nonneg_left hb.2 (inv_nonneg.mpr hn'.le)
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_right hcard hnonneg
      have hh := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hn'.le)
      simpa only [← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul] using hh

lemma proposition4b_ht_L2 (M : Study) (hM : ValidStudy M) :
    MemLp (fun o => htTerm (M.pi (W o)) (X o) (Y o)) 2 M.law := by
  letI := hM.probability
  have mx : Measurable X := (measurable_of_countable bit).comp measurable_snd.fst
  have my : Measurable Y1 := (measurable_of_countable bit).comp measurable_snd.snd.snd
  have mh : Measurable (fun o => htTerm (M.pi (W o)) (X o) (Y o)) := by
    simp only [htTerm, consistency_treated]
    exact (mx.mul my).div (hM.measurable_pi.comp measurable_fst)
  apply memLp_of_bounded (a := 0) (b := M.delta⁻¹) _ mh.aestronglyMeasurable 2
  filter_upwards [hM.positivity] with o ho
  have hh := ht_binary_range (M.pi (W o)) M.delta ho.1 hM.delta_pos o.2.1 o.2.2.2
  simpa only [htTerm, consistency_treated] using ⟨hh.1, hh.2.le⟩

lemma proposition4b_ht_scaled_moment (M : Study) (hM : ValidStudy M) (n : ℕ) (hn : 0 < n) :
    Integrable (fun a => (Real.sqrt n * (ht M a - mu M))^2) (sampleLaw M n) ∧
    (∫ a, (Real.sqrt n * (ht M a - mu M))^2 ∂sampleLaw M n) =
      variance (fun o => htTerm (M.pi (W o)) (X o) (Y o)) M.law := by
  letI := hM.probability
  have hf := proposition4b_ht_L2 M hM
  have hmean : MemLp (ht M (n := n)) 2 (sampleLaw M n) := by
    have hsum : MemLp (fun a : Sample n => ∑ i, htTerm (M.pi (W (a i))) (X (a i)) (Y (a i)))
        2 (sampleLaw M n) := memLp_finsetSum _ (fun i _ => hf.comp_measurePreserving
          (measurePreserving_eval (fun _ : Fin n => M.law) i))
    have hfun : ht M (n := n) = fun a =>
        (∑ i, htTerm (M.pi (W (a i))) (X (a i)) (Y (a i))) * (n : ℝ)⁻¹ := by
      funext a
      exact div_eq_mul_inv _ _
    rw [hfun]
    exact hsum.mul_const _

  have hscaled := (hmean.sub (memLp_const (mu M))).const_mul (Real.sqrt n)
  refine ⟨hscaled.integrable_sq, ?_⟩
  have hv := iid_mean_variance M.law _ hf n hn
  change variance (ht M (n := n)) (sampleLaw M n) = _ at hv
  have he : (∫ a, (ht M a - mu M)^2 ∂sampleLaw M n) =
      variance (ht M (n := n)) (sampleLaw M n) := by
    rw [variance_eq_integral hmean.aemeasurable, ht_unbiased M hM n hn]
  simp_rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [integral_const_mul, he, hv]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp


lemma proposition4b_adjusted_measurable (M : Study) (hM : ValidStudy M) (n : ℕ)
    (F : CrossFit n) : Measurable (adjusted M F) := by
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
  have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have my : Measurable Y := ((measurable_const.sub mx).mul my0).add (mx.mul my1)
  unfold adjusted
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i hi
  have mi := measurable_pi_apply i (X := fun _ : Fin n => Unit)
  have mw : Measurable (fun a : Sample n => W (a i)) := measurable_fst.comp mi
  have mg := (F.measurable_g (F.fold i)).comp (measurable_id.prodMk mw)
  exact (((mx.comp mi).mul ((my.comp mi).sub mg)).div (hM.measurable_pi.comp mw)).add mg

lemma proposition4b_total_moment (M : Study) (hM : ValidStudy M) (n : ℕ) (hn : 0 < n)
    (F : CrossFit n)
    (hfits : ∀ j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => F.g j a (W o)) 2 M.law)
    (hnorm : ∀ j, Integrable (fun a => l2Sq M (F.g j a)) (sampleLaw M n)) :
    Integrable (fun a => (Real.sqrt n * (adjusted M F a - mu M))^2) (sampleLaw M n) ∧
    (∫ a, (Real.sqrt n * (adjusted M F a - mu M))^2 ∂sampleLaw M n) ≤
      3 * variance (fun o => htTerm (M.pi (W o)) (X o) (Y o)) M.law +
      3 * (1+M.delta⁻¹)^2 * ((∫ a, l2Sq M (F.g false a) ∂sampleLaw M n) +
        (∫ a, l2Sq M (F.g true a) ∂sampleLaw M n)) := by
  let A : Sample n → ℝ := fun a => Real.sqrt n * (ht M a - mu M)
  let B : Bool → Sample n → ℝ := fun j a => Real.sqrt n * foldRemainder M F j (fun _ => 0) a
  let Z : Sample n → ℝ := fun a => Real.sqrt n * (adjusted M F a - mu M)
  have hA := proposition4b_ht_scaled_moment M hM n hn
  have hB := fun j => proposition4b_fold_scaled_bound M hM n hn F j (hfits j) (hnorm j)
  have hpoint : ∀ a, Z a = A a + B false a + B true a := by
    intro a
    have h := crossfit_decomposition M F (fun _ _ => 0) a
    have hl : leading M F (fun _ _ => 0) a = ht M a := by
      simp only [leading, ht, adjustedTerm, htTerm, sub_zero, add_zero]
    rw [hl] at h
    dsimp [Z, A, B]
    rw [h]
    ring
  have hb : ∀ a, (Z a)^2 ≤ 3 * ((A a)^2 + (B false a)^2 + (B true a)^2) := by
    intro a
    rw [hpoint]
    nlinarith only [sq_nonneg (A a - B false a), sq_nonneg (A a - B true a),
      sq_nonneg (B false a - B true a)]
  have hidom : Integrable (fun a => 3 * ((A a)^2 + (B false a)^2 + (B true a)^2)) (sampleLaw M n) :=
    ((hA.1.add (hB false).1).add (hB true).1).const_mul 3
  have hiZ : Integrable (fun a => (Z a)^2) (sampleLaw M n) := by
    apply hidom.mono' ((((proposition4b_adjusted_measurable M hM n F).sub_const (mu M)).const_mul
      (Real.sqrt n)).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun a => by
      change ‖(Z a)^2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Z a))]
      exact hb a
  refine ⟨hiZ, ?_⟩
  have ht := integral_mono_ae hiZ hidom (Filter.Eventually.of_forall hb)
  have ia : Integrable (fun a => (A a)^2) (sampleLaw M n) := hA.1
  have ib : Integrable (fun a => (B false a)^2) (sampleLaw M n) := (hB false).1
  have ic : Integrable (fun a => (B true a)^2) (sampleLaw M n) := (hB true).1
  have iab : Integrable (fun a => (A a)^2 + (B false a)^2) (sampleLaw M n) := ia.add ib
  rw [integral_const_mul, integral_add iab ic, integral_add ia ib] at ht
  change (∫ a, (Z a)^2 ∂sampleLaw M n) ≤ _
  have hAe : (∫ a, (A a)^2 ∂sampleLaw M n) =
      variance (fun o => htTerm (M.pi (W o)) (X o) (Y o)) M.law := hA.2
  rw [hAe] at ht
  nlinarith only [ht, (hB false).2, (hB true).2]

 theorem proposition4b_proof (M : Study) (hM : ValidStudy M) (F : ∀ n, CrossFit n)
    (hbal : Balanced F) (g : Bool → ℝ → ℝ)
    (hg : ∀ j, MemLp (fun o => g j (W o)) 2 M.law)
    (hconv : ∀ j, L2InMeanSquare M F j (g j))
    (hfitsL2 : ∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law) :
    RootN M (fun n => adjusted M (F n)) := by
  letI := hM.probability
  intro eps heps
  let v := variance (fun o => htTerm (M.pi (W o)) (X o) (Y o)) M.law
  let K := 1 + 3 * v + 3 * (1+M.delta⁻¹)^2 * (4 + 2 * l2Sq M (g false) + 2 * l2Sq M (g true))
  have hv : 0 ≤ v := variance_nonneg _ _
  have hg0 : 0 ≤ l2Sq M (g false) := integral_nonneg fun o => sq_nonneg _
  have hg1 : 0 ≤ l2Sq M (g true) := integral_nonneg fun o => sq_nonneg _
  have hK : 0 < K := by dsimp [K]; positivity
  let C := Real.sqrt (K / eps)
  have hC : 0 < C := Real.sqrt_pos.2 (div_pos hK heps)
  have hCsq : C^2 = K / eps := Real.sq_sqrt (div_nonneg hK.le heps.le)
  refine ⟨C, hC, ?_⟩
  have hsmall : ∀ j : Bool, ∀ᶠ n in atTop,
      (∫ a, l2Sq M (fun w => (F n).g j a w - g j w) ∂sampleLaw M n) < 1 := by
    intro j
    exact (tendsto_order.1 (hconv j).1).2 1 (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hsmall false).and (hsmall true))
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hNn := hN n (le_trans (le_max_left _ _) hn)
  have hpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hn)
  have hnorm := fun j => proposition4b_fit_norm_integrable M hM n (F n) j (g j) (hg j)
    (hfitsL2 n j) ((hconv j).2 n)
  have hm := proposition4b_total_moment M hM n hpos (F n) (hfitsL2 n) (fun j => (hnorm j).1)
  have hbound : (∫ a, (Real.sqrt n * (adjusted M (F n) a - mu M))^2 ∂sampleLaw M n) ≤ K := by
    have h0 := (hnorm false).2
    have h1 := (hnorm true).2
    have hsum : (∫ a, l2Sq M ((F n).g false a) ∂sampleLaw M n) +
        (∫ a, l2Sq M ((F n).g true a) ∂sampleLaw M n) ≤
        4 + 2 * l2Sq M (g false) + 2 * l2Sq M (g true) := by linarith only [hNn.1, hNn.2, h0, h1]
    have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 3 * (1+M.delta⁻¹)^2 by positivity)
    dsimp [K, v]
    linarith only [hm.2, hmul]
  have hsub : {a : Sample n | C < Real.sqrt n * |adjusted M (F n) a - mu M|} ⊆
      {a | C^2 ≤ (Real.sqrt n * (adjusted M (F n) a - mu M))^2} := by
    intro a ha
    have habs : |Real.sqrt n * (adjusted M (F n) a - mu M)| =
        Real.sqrt n * |adjusted M (F n) a - mu M| := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    change C < _ at ha
    rw [← habs] at ha
    change C^2 ≤ (Real.sqrt n * (adjusted M (F n) a - mu M))^2
    have hs := (sq_le_sq₀ hC.le (abs_nonneg (Real.sqrt n * (adjusted M (F n) a - mu M)))).2 ha.le
    simpa only [sq_abs] using hs
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun a : Sample n => sq_nonneg (Real.sqrt n * (adjusted M (F n) a - mu M))) hm.1 (C^2)
  have hmono := measureReal_mono (μ := sampleLaw M n) hsub
  have ht := (mul_le_mul_of_nonneg_left hmono (sq_nonneg C)).trans (hmark.trans hbound)
  have heq : eps * C^2 = K := by rw [hCsq]; field_simp [heps.ne'] <;> ring
  change (sampleLaw M n).real _ ≤ eps
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hC)).mp
  calc
    _ ≤ K := ht
    _ = C^2 * eps := by rw [← heq, mul_comm eps (C^2)]


end
end AronowAudit.P046.Wave1
