import SAP.P046.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.WH.W1.P.T3_L3

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

lemma local_ht_bits (M : Study) {n : ℕ} (a : Sample n) :
    ht M a = (∑ i, bit ((a i).2.1 && (a i).2.2.2) / M.pi (W (a i))) / n := by
  unfold ht
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [htTerm]
  rcases a i with ⟨w, x, y0, y1⟩
  cases x <;> cases y1 <;> simp [X, Y, Y0, Y1, bit]

lemma random_threshold_good (M : Study) (hM : ValidStudy M) (n : ℕ) :
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

lemma random_threshold_expansion (M : Study) (hM : ValidStudy M)
    (n : ℕ) (c : ℝ) :
    condExp (sampleCovariateSigma n) (sampleLaw M n)
      (fun a => if Real.sqrt (xi M a) * c ≤ |ht M a - muW M a| then (1 : ℝ) else 0)
      =ᵐ[sampleLaw M n] fun a =>
        ∑ b : Fin n → Bool,
          (if Real.sqrt (xi M a) * c ≤
              |(∑ i, bit (b i) / M.pi (W (a i))) / n - muW M a|
            then (1 : ℝ) else 0) * ∏ i, AronowAudit.P046.Wave1.p3_weight (Bridge.toStudy M) (b i) (W (a i)) := by
  classical
  letI := hM.probability
  let P := sampleLaw M n
  let C (b : Fin n → Bool) (a : Sample n) : ℝ :=
    if Real.sqrt (xi M a) * c ≤
      |(∑ i, bit (b i) / M.pi (W (a i))) / n - muW M a| then 1 else 0
  let J (b : Fin n → Bool) (a : Sample n) : ℝ := ∏ i, AronowAudit.P046.Wave1.p3_indicator (b i) (a i)
  let f (a : Sample n) : ℝ :=
    if Real.sqrt (xi M a) * c ≤ |ht M a - muW M a| then 1 else 0
  have mc : Measurable (covariates (n := n)) :=
    measurable_pi_lambda (fun j => measurable_fst.comp (measurable_pi_apply j))
  have hle : sampleCovariateSigma n ≤ (inferInstance : MeasurableSpace (Sample n)) := mc.comap_le
  have mC (b) : Measurable[sampleCovariateSigma n] (C b) := by
    letI instRandomThresholdCovariateMeasurable : MeasurableSpace (Sample n) :=
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
    have mxi : Measurable[sampleCovariateSigma n] (xi M (n := n)) :=
      (Finset.measurable_sum Finset.univ (fun i _ => (mp i).inv.pow_const 2)).div_const n
    have mr : Measurable[sampleCovariateSigma n] (muW M (n := n)) :=
      (Finset.measurable_sum Finset.univ (fun i _ => mm i)).div_const n
    have mh : Measurable[sampleCovariateSigma n]
        (fun a : Sample n => (∑ i, bit (b i) / M.pi (W (a i))) / n) :=
      (Finset.measurable_sum Finset.univ
        (fun i _ => measurable_const.div (mp i))).div_const n
    exact measurable_const.ite
      (measurableSet_le (mxi.sqrt.mul_const c) (mh.sub mr).abs) measurable_const
  have mJ (b) : Measurable (J b) :=
    Finset.measurable_prod Finset.univ
      (fun i _ => (AronowAudit.P046.Wave1.p3_indicator_measurable (b i)).comp (measurable_pi_apply i))
  have iCJ (b) : Integrable (fun a => C b a * J b a) P := by
    apply memLp_one_iff_integrable.1 (memLp_of_bounded (a := 0) (b := 1) _
      (((mC b).mono hle le_rfl).mul (mJ b)).aestronglyMeasurable 1)
    exact ae_of_all _ (fun a => by
      dsimp [J]
      rw [AronowAudit.P046.Wave1.p3_product_indicator]
      dsimp [C]
      split <;> split <;> norm_num)
  have hJ (b) : condExp (sampleCovariateSigma n) P (J b) =ᵐ[P]
      fun a => ∏ i, AronowAudit.P046.Wave1.p3_weight (Bridge.toStudy M) (b i) (W (a i)) := by
    apply AronowAudit.P046.Wave1.p3_product_conditional (Bridge.toStudy M) (Bridge.valid_to hM) n (fun i => AronowAudit.P046.Wave1.p3_indicator (b i))
      (fun i => AronowAudit.P046.Wave1.p3_weight (Bridge.toStudy M) (b i)) (fun i => AronowAudit.P046.Wave1.p3_indicator_measurable (b i))
    · intro i
      cases b i
      · change Measurable (fun w : ℝ => 1 - M.pi w * M.m w)
        exact measurable_const.sub (hM.measurable_pi.mul hM.measurable_m)
      · change Measurable (fun w : ℝ => M.pi w * M.m w)
        exact hM.measurable_pi.mul hM.measurable_m
    · exact fun i => AronowAudit.P046.Wave1.p3_indicator_integrable (Bridge.toStudy M) (Bridge.valid_to hM) (b i)
    · exact fun i => AronowAudit.P046.Wave1.p3_single_conditional (Bridge.toStudy M) (Bridge.valid_to hM) (b i)
  have heq : f = fun a => ∑ b : Fin n → Bool, C b a * J b a := by
    funext a
    rw [Finset.sum_eq_single (fun i => (a i).2.1 && (a i).2.2.2)]
    · simp only [J, AronowAudit.P046.Wave1.p3_product_indicator, if_true, mul_one]
      simp only [f, C]
      rw [local_ht_bits]
    · intro b _ hb
      simp only [J, AronowAudit.P046.Wave1.p3_product_indicator, if_neg (Ne.symm hb), mul_zero]
    · simp
  have hpull (b) : condExp (sampleCovariateSigma n) P (fun a => C b a * J b a) =ᵐ[P]
      fun a => C b a * ∏ i, AronowAudit.P046.Wave1.p3_weight (Bridge.toStudy M) (b i) (W (a i)) := by
    have iJ : Integrable (J b) P :=
      Integrable.fintype_prod (fun i => AronowAudit.P046.Wave1.p3_indicator_integrable (Bridge.toStudy M) (Bridge.valid_to hM) (b i))
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

end
end SAP.P046.WH.W1.P.T3_L3

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal
open SAP.P046 SAP.P046.WH.W1

theorem SAP.P046.WH.W1.T3_L3_proof : SAP.P046.WH.W1.T3_L3 := by
  classical
  intro M hM n hn alpha ha
  letI := hM.probability
  let c := wholeC n alpha
  have hc : ∀ᵐ a ∂sampleLaw M n,
      condExp (sampleCovariateSigma n) (sampleLaw M n)
        (fun b => if Real.sqrt (xi M b) * c ≤ |ht M b - muW M b| then (1 : ℝ) else 0) a ≤ alpha / 2 := by
    have hexp := SAP.P046.WH.W1.P.T3_L3.random_threshold_expansion M hM n c
    have hgood := SAP.P046.WH.W1.P.T3_L3.random_threshold_good M hM n
    filter_upwards [hexp, hgood] with a hexp hg
    have hp (i) : 0 < M.pi (W (a i)) := lt_trans hM.delta_pos (hg i).1
    have hr (i) : 0 ≤ M.pi (W (a i)) * M.m (W (a i)) ∧
        M.pi (W (a i)) * M.m (W (a i)) ≤ 1 := by
      refine ⟨mul_nonneg (hp i).le (hg i).2.2.1, ?_⟩
      calc
        _ ≤ M.pi (W (a i)) * 1 := mul_le_mul_of_nonneg_left (hg i).2.2.2 (hp i).le
        _ ≤ 1 := by simp only [mul_one]; linarith [(hg i).2.1, hM.delta_pos]
    have hxi : 0 < xi M a := by
      apply div_pos _ (Nat.cast_pos.mpr hn)
      exact Finset.sum_pos (fun i _ => sq_pos_of_pos (inv_pos.mpr (hp i)))
        ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    let r : Fin n → Set.Icc (0 : ℝ) 1 :=
      fun i => ⟨M.pi (W (a i)) * M.m (W (a i)), hr i⟩
    let Q := Measure.pi (fun i => bernoulliMeasure true false (r i))
    have hQ : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
    letI := hQ
    have hh := AronowAudit.P046.Wave1.p3_bernoulli_tail n hn (fun i => M.pi (W (a i)))
      (fun i => M.m (W (a i))) hp hr (Real.sqrt (xi M a) * c)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    change Q.real _ ≤ _ at hh
    have hex : -2 * (n : ℝ) * (Real.sqrt (xi M a) * c)^2 / xi M a =
        -2 * (n : ℝ) * c^2 := by
      rw [mul_pow, Real.sq_sqrt hxi.le]
      field_simp
    change Q.real _ ≤ 2 * Real.exp
      (-2 * (n : ℝ) * (Real.sqrt (xi M a) * c)^2 / xi M a) at hh
    rw [hex] at hh
    let A : Set (Fin n → Bool) := {b | Real.sqrt (xi M a) * c ≤
      |(∑ i, bit (b i) / M.pi (W (a i))) / n - (∑ i, M.m (W (a i))) / n|}
    have mA : MeasurableSet A := Set.toFinite A |>.measurableSet
    have hprob_eq : Q.real A = ∑ b : Fin n → Bool,
        (if Real.sqrt (xi M a) * c ≤
          |(∑ i, bit (b i) / M.pi (W (a i))) / n - (∑ i, M.m (W (a i))) / n|
          then (1 : ℝ) else 0) * ∏ i, AronowAudit.P046.Wave1.p3_weight
            (Bridge.toStudy M) (b i) (W (a i)) := by
      dsimp [A]
      rw [← integral_indicator_one mA, integral_fintype Integrable.of_finite]
      apply Finset.sum_congr rfl
      intro b _
      have hb : Q.real {b} = ∏ i, AronowAudit.P046.Wave1.p3_weight
          (Bridge.toStudy M) (b i) (W (a i)) := by
        have hs : ({b} : Set (Fin n → Bool)) = Set.univ.pi (fun i => {b i}) := by
          ext d
          simp [funext_iff, Set.mem_pi]
        change (Q {b}).toReal = _
        dsimp only [Q]
        rw [hs, Measure.pi_pi, ENNReal.toReal_prod]
        apply Finset.prod_congr rfl
        intro i _
        change (bernoulliMeasure true false (r i)).real {b i} = _
        cases b i <;> simp [AronowAudit.P046.Wave1.p3_weight, r, Bridge.toStudy]
      rw [hb]
      simp [Set.indicator, A]
    have hbound : 2 * Real.exp (-2 * (n : ℝ) * c^2) ≤ alpha / 2 := by
      have he := whole_exp n hn alpha ha
      simpa [c] using (he.1.trans he.2).le
    have hq : Q.real A ≤ alpha / 2 := by
      exact hh.trans hbound
    rw [hexp]
    change (∑ b : Fin n → Bool,
        (if Real.sqrt (xi M a) * c ≤
          |(∑ i, bit (b i) / M.pi (W (a i))) / n - muW M a|
          then (1 : ℝ) else 0) * ∏ i, AronowAudit.P046.Wave1.p3_weight
            (Bridge.toStudy M) (b i) (W (a i))) ≤ alpha / 2
    have hsum_eq : (∑ b : Fin n → Bool,
        (if Real.sqrt (xi M a) * c ≤
          |(∑ i, bit (b i) / M.pi (W (a i))) / n - muW M a|
          then (1 : ℝ) else 0) * ∏ i, AronowAudit.P046.Wave1.p3_weight
            (Bridge.toStudy M) (b i) (W (a i))) = Q.real A := by
      rw [hprob_eq]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : Real.sqrt (xi M a) * c ≤
          |(∑ i, bit (b i) / M.pi (W (a i))) / n - (∑ i, M.m (W (a i))) / n|
      · simp [hb, muW]
      · simp [hb, muW]
    rw [hsum_eq]
    exact hq
  have hcond :
      ∀ᵐ a ∂sampleLaw M n,
        condExp (sampleCovariateSigma n) (sampleLaw M n)
          (fun b => if Real.sqrt (xi M b) * wholeC n alpha ≤ |ht M b - muW M b|
            then (1 : ℝ) else 0) a ≤ alpha / 2 := by
    simpa [c] using hc
  have hgood := SAP.P046.WH.W1.P.T3_L3.random_threshold_good M hM n
  have hcancel : ∀ᵐ a ∂sampleLaw M n,
      2 * Real.exp (-2 * (n : ℝ) * (Real.sqrt (xi M a) * wholeC n alpha)^2 / xi M a) =
        2 * Real.exp (-2 * (n : ℝ) * (wholeC n alpha)^2) := by
    filter_upwards [hgood] with a hg
    have hp (i) : 0 < M.pi (W (a i)) := lt_trans hM.delta_pos (hg i).1
    have hxi : 0 < xi M a := by
      apply div_pos _ (Nat.cast_pos.mpr hn)
      exact Finset.sum_pos (fun i _ => sq_pos_of_pos (inv_pos.mpr (hp i)))
        ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    congr 1
    rw [mul_pow, Real.sq_sqrt hxi.le]
    field_simp
  have hun := AronowAudit.P046.Wave1.p3_random_tail
    (Bridge.toStudy M) (Bridge.valid_to hM) n hn (wholeC n alpha) (Real.sqrt_nonneg _)
  have htail : 2 * Real.exp (-2 * (n : ℝ) * (wholeC n alpha)^2) ≤ alpha / 2 := by
    have he := whole_exp n hn alpha ha
    exact (he.1.trans he.2).le
  refine ⟨hcond.and hcancel, ?_⟩
  change (sampleLaw M n (wholeConditionalError M n alpha)).toReal ≤ alpha / 2
  have hun' : (sampleLaw M n (wholeConditionalError M n alpha)).toReal ≤
      2 * Real.exp (-2 * (n : ℝ) * (wholeC n alpha)^2) := by
    change (AronowAudit.P046.sampleLaw (Bridge.toStudy M) n).real
      {a | Real.sqrt (AronowAudit.P046.xi (Bridge.toStudy M) a) * wholeC n alpha ≤
        |AronowAudit.P046.ht (Bridge.toStudy M) a - AronowAudit.P046.muW (Bridge.toStudy M) a|} ≤ _
    exact hun
  exact hun'.trans htail

