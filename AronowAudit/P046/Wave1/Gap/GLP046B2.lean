import AronowAudit.P046.Wave1.Gap.GP046B2

/-!
P046-T3: conditional Hoeffding with the conditional centre `muW`.

Expanding the event indicator over all bit vectors identifies its conditional
expectation with the finite product Bernoulli tail, before unconditional
integration. The bound uses the binary conditional table, its product-sampling
lift, and the heterogeneous Bernoulli Hoeffding inequality.
-/

namespace AronowAudit.P046.Wave1

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

set_option maxHeartbeats 500000
set_option linter.style.haveILetI false

/-- Conditional expectation of the tail indicator as a finite sum over the
conditional product Bernoulli law. No sign restriction on the threshold is needed. -/
lemma conditional_hoeffding_binary_expansion (M : Study) (hM : ValidStudy M)
    (n : ℕ) (t : ℝ) :
    condExp (sampleCovariateSigma n) (sampleLaw M n)
      (fun a => if t ≤ |ht M a - muW M a| then (1 : ℝ) else 0)
      =ᵐ[sampleLaw M n] fun a =>
        ∑ b : Fin n → Bool,
          (if t ≤ |(∑ i, bit (b i) / M.pi (W (a i))) / n - muW M a|
            then (1 : ℝ) else 0) * ∏ i, p3_weight M (b i) (W (a i)) := by
  classical
  letI := hM.probability
  let P := sampleLaw M n
  let C (b : Fin n → Bool) (a : Sample n) : ℝ :=
    if t ≤ |(∑ i, bit (b i) / M.pi (W (a i))) / n - muW M a| then 1 else 0
  let J (b : Fin n → Bool) (a : Sample n) : ℝ := ∏ i, p3_indicator (b i) (a i)
  let f (a : Sample n) : ℝ := if t ≤ |ht M a - muW M a| then 1 else 0
  have mc : Measurable (covariates (n := n)) :=
    measurable_pi_lambda (fun j => measurable_fst.comp (measurable_pi_apply j))
  have hle : sampleCovariateSigma n ≤ (inferInstance : MeasurableSpace (Sample n)) :=
    mc.comap_le
  have mC (b) : Measurable[sampleCovariateSigma n] (C b) := by
    letI instConditionalHoeffdingCovariateMeasurable : MeasurableSpace (Sample n) :=
      sampleCovariateSigma n
    have mp (i : Fin n) :
        Measurable[sampleCovariateSigma n] (fun a : Sample n => M.pi (W (a i))) :=
      ((hM.measurable_pi.comp
        (show Measurable (fun w : Fin n → ℝ => w i) from measurable_pi_apply i)).comp
          (comap_measurable (covariates (n := n))))
    have mm (i : Fin n) :
        Measurable[sampleCovariateSigma n] (fun a : Sample n => M.m (W (a i))) :=
      ((hM.measurable_m.comp
        (show Measurable (fun w : Fin n → ℝ => w i) from measurable_pi_apply i)).comp
          (comap_measurable (covariates (n := n))))
    have mr : Measurable[sampleCovariateSigma n] (muW M (n := n)) :=
      (Finset.measurable_sum Finset.univ (fun i _ => mm i)).div_const n
    have mh : Measurable[sampleCovariateSigma n]
        (fun a : Sample n => (∑ i, bit (b i) / M.pi (W (a i))) / n) :=
      (Finset.measurable_sum Finset.univ
        (fun i _ => measurable_const.div (mp i))).div_const n
    exact measurable_const.ite (measurableSet_le measurable_const (mh.sub mr).abs)
      measurable_const
  have mJ (b) : Measurable (J b) :=
    Finset.measurable_prod Finset.univ
      (fun i _ => (p3_indicator_measurable (b i)).comp (measurable_pi_apply i))
  have iCJ (b) : Integrable (fun a => C b a * J b a) P := by
    apply memLp_one_iff_integrable.1 (memLp_of_bounded (a := 0) (b := 1) _
      (((mC b).mono hle le_rfl).mul (mJ b)).aestronglyMeasurable 1)
    exact ae_of_all _ (fun a => by
      dsimp [J]
      rw [p3_product_indicator]
      dsimp [C]
      split <;> split <;> norm_num)
  have hJ (b) : condExp (sampleCovariateSigma n) P (J b) =ᵐ[P]
      fun a => ∏ i, p3_weight M (b i) (W (a i)) := by
    apply p3_product_conditional M hM n (fun i => p3_indicator (b i))
      (fun i => p3_weight M (b i)) (fun i => p3_indicator_measurable (b i))
    · intro i
      cases b i
      · change Measurable (fun w : ℝ => 1 - M.pi w * M.m w)
        exact measurable_const.sub (hM.measurable_pi.mul hM.measurable_m)
      · change Measurable (fun w : ℝ => M.pi w * M.m w)
        exact hM.measurable_pi.mul hM.measurable_m
    · exact fun i => p3_indicator_integrable M hM (b i)
    · exact fun i => p3_single_conditional M hM (b i)
  have heq : f = fun a => ∑ b : Fin n → Bool, C b a * J b a := by
    funext a
    rw [Finset.sum_eq_single (fun i => (a i).2.1 && (a i).2.2.2)]
    · simp only [J, p3_product_indicator, if_true, mul_one]
      simp only [f, C, p3_ht_bits]
    · intro b _ hb
      simp only [J, p3_product_indicator, if_neg (Ne.symm hb), mul_zero]
    · simp
  have hpull (b) : condExp (sampleCovariateSigma n) P (fun a => C b a * J b a) =ᵐ[P]
      fun a => C b a * ∏ i, p3_weight M (b i) (W (a i)) := by
    have iJ : Integrable (J b) P :=
      Integrable.fintype_prod (fun i => p3_indicator_integrable M hM (b i))
    have h := condExp_mul_of_stronglyMeasurable_left (mC b).stronglyMeasurable (iCJ b) iJ
    exact h.trans ((hJ b).mono (fun a ha => congrArg (fun x => C b a * x) ha))
  have hs := condExp_finsetSum (μ := P)
    (fun b (_ : b ∈ (Finset.univ : Finset (Fin n → Bool))) => iCJ b)
      (sampleCovariateSigma n)
  simp only [Finset.sum_fn] at hs
  have ha := ae_all_iff.2 hpull
  filter_upwards [hs, ha] with a hs ha
  change condExp (sampleCovariateSigma n) P f a = _
  rw [heq]
  exact hs.trans (Finset.sum_congr rfl (fun b _ => ha b))

/-- One common full-probability set on which every sample coordinate satisfies
positivity and the regression range bound. -/
lemma conditional_hoeffding_good (M : Study) (hM : ValidStudy M) (n : ℕ) :
    ∀ᵐ a ∂sampleLaw M n, ∀ i : Fin n,
      M.delta < M.pi (W (a i)) ∧ M.pi (W (a i)) < 1 - M.delta ∧
        0 ≤ M.m (W (a i)) ∧ M.m (W (a i)) ≤ 1 := by
  letI := hM.probability
  apply ae_all_iff.2
  intro i
  have hu : ∀ᵐ o ∂M.law,
      M.delta < M.pi (W o) ∧ M.pi (W o) < 1 - M.delta ∧
        0 ≤ M.m (W o) ∧ M.m (W o) ≤ 1 := by
    filter_upwards [hM.positivity, hM.regression_range] with o hp hm
    exact ⟨hp.1, hp.2, hm⟩
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => M.law) (i := i)).eventually hu

/-- T3(ii): conditional Hoeffding centred at `muW`, with the actual sample law
and the random heterogeneous-width statistic `xi`. -/
theorem conditional_hoeffding_proof (M : Study) (hM : ValidStudy M)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht0 : 0 ≤ t) :
    ∀ᵐ a ∂sampleLaw M n,
      condExp (sampleCovariateSigma n) (sampleLaw M n)
        (fun b => if t ≤ |ht M b - muW M b| then (1 : ℝ) else 0) a ≤
          2 * Real.exp (-2 * n * t^2 / xi M a) := by
  classical
  letI := hM.probability
  filter_upwards [conditional_hoeffding_binary_expansion M hM n t,
    conditional_hoeffding_good M hM n] with a hc hg
  have hp (i) : 0 < M.pi (W (a i)) := lt_trans hM.delta_pos (hg i).1
  have hr (i) : 0 ≤ M.pi (W (a i)) * M.m (W (a i)) ∧
      M.pi (W (a i)) * M.m (W (a i)) ≤ 1 := by
    refine ⟨mul_nonneg (hp i).le (hg i).2.2.1, ?_⟩
    calc
      _ ≤ M.pi (W (a i)) * 1 := mul_le_mul_of_nonneg_left (hg i).2.2.2 (hp i).le
      _ ≤ 1 := by simp only [mul_one]; linarith [(hg i).2.1, hM.delta_pos]
  let r : Fin n → Set.Icc (0 : ℝ) 1 :=
    fun i => ⟨M.pi (W (a i)) * M.m (W (a i)), hr i⟩
  let Q := Measure.pi (fun i => bernoulliMeasure true false (r i))
  have hQ : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
  letI := hQ
  have hh := p3_bernoulli_tail n hn (fun i => M.pi (W (a i)))
    (fun i => M.m (W (a i))) hp hr t ht0
  change Q.real _ ≤ 2 * Real.exp (-2 * (n : ℝ) * t^2 / xi M a) at hh
  rw [hc]
  convert hh using 1
  let A : Set (Fin n → Bool) :=
    {b | t ≤ |(∑ i, bit (b i) / M.pi (W (a i))) / n - (∑ i, M.m (W (a i))) / n|}
  have mA : MeasurableSet A := Set.toFinite A |>.measurableSet
  rw [← integral_indicator_one mA, integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro b _
  have hb : Q.real {b} = ∏ i, p3_weight M (b i) (W (a i)) := by
    have hs : ({b} : Set (Fin n → Bool)) = Set.univ.pi (fun i => {b i}) := by
      ext d
      simp [funext_iff, Set.mem_pi]
    change (Q {b}).toReal = _
    dsimp only [Q]
    rw [hs, Measure.pi_pi, ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    change (bernoulliMeasure true false (r i)).real {b i} = _
    cases b i <;> simp [p3_weight, r]
  rw [hb]
  by_cases h : t ≤
      |(∑ i, bit (b i) / M.pi (W (a i))) / n - (∑ i, M.m (W (a i))) / n| <;>
    simp [A, muW, Set.indicator, h]

end

end AronowAudit.P046.Wave1
