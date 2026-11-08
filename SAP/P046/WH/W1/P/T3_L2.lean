import SAP.P046.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace SAP.P046.WH.W1.P.T3_L2

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal
open Classical

private abbrev p3_indicator := AronowAudit.P046.Wave1.p3_indicator

private def p3_weight (M : Study) (b : Bool) (w : ℝ) : ℝ :=
  AronowAudit.P046.Wave1.p3_weight (Bridge.toStudy M) b w

private lemma p3_weight_sum (M : Study) (w : ℝ) :
    p3_weight M true w + p3_weight M false w = 1 := by
  change (M.pi w * M.m w) + (1 - M.pi w * M.m w) = 1
  ring

private theorem p3_indicator_measurable (b : Bool) : Measurable (p3_indicator b) :=
  AronowAudit.P046.Wave1.p3_indicator_measurable b

private theorem p3_indicator_integrable (M : Study) (hM : ValidStudy M) (b : Bool) :
    Integrable (p3_indicator b) M.law := by
  exact AronowAudit.P046.Wave1.p3_indicator_integrable
    (Bridge.toStudy M) (Bridge.valid_to hM) b

private theorem p3_single_conditional (M : Study) (hM : ValidStudy M) (b : Bool) :
    condExp covariateSigma M.law (p3_indicator b) =ᵐ[M.law]
      fun o => p3_weight M b (W o) := by
  convert (AronowAudit.P046.Wave1.p3_single_conditional
    (Bridge.toStudy M) (Bridge.valid_to hM) b) using 1 <;> rfl

private theorem p3_product_conditional (M : Study) (hM : ValidStudy M) (n : ℕ)
    (f : Fin n → Unit → ℝ) (k : Fin n → ℝ → ℝ)
    (mf : ∀ i, Measurable (f i)) (mk : ∀ i, Measurable (k i))
    (hf : ∀ i, Integrable (f i) M.law)
    (hc : ∀ i, condExp covariateSigma M.law (f i) =ᵐ[M.law]
      fun o => k i (W o)) :
    condExp (sampleCovariateSigma n) (sampleLaw M n) (fun a => ∏ i, f i (a i))
      =ᵐ[sampleLaw M n] fun a => ∏ i, k i (W (a i)) := by
  convert (AronowAudit.P046.Wave1.p3_product_conditional
    (Bridge.toStudy M) (Bridge.valid_to hM) n f k mf mk hf hc) using 1 <;> rfl

private theorem p3_product_indicator (n : ℕ) (b : Fin n → Bool) (a : Sample n) :
    (∏ i, p3_indicator (b i) (a i)) =
      if (fun i => (a i).2.1 && (a i).2.2.2) = b then (1 : ℝ) else 0 := by
  exact AronowAudit.P046.Wave1.p3_product_indicator n b a

private lemma wholeSummand_binary (M : Study) (n : ℕ) (i : Fin n) (a : Sample n) :
    wholeSummand M i a =
      (if (a i).2.1 && (a i).2.2.2 then 1 else 0) /
        ((n : ℝ) * M.pi (W (a i))) := by
  cases hx : (a i).2.1 <;> cases hy : (a i).2.2.2 <;>
    simp [wholeSummand, X, Y, Y1, bit, hx, hy]

private lemma wholeSummand_measurable (M : Study) (hM : ValidStudy M) {n : ℕ}
    (i : Fin n) : Measurable (wholeSummand M i) := by
  have mx : Measurable (fun a : Sample n => X (a i)) :=
    measurable_X.comp (measurable_pi_apply i)
  have my : Measurable (fun a : Sample n => Y (a i)) :=
    measurable_Y.comp (measurable_pi_apply i)
  have mp : Measurable (fun a : Sample n => M.pi (W (a i))) :=
    hM.measurable_pi.comp (measurable_fst.comp (measurable_pi_apply i))
  exact (mx.mul my).div (measurable_const.mul mp)

private lemma p3_coordinate_conditional (M : Study) (hM : ValidStudy M) {n : ℕ}
    (i : Fin n) (b : Bool) :
    condExp (sampleCovariateSigma n) (sampleLaw M n)
      (fun a => p3_indicator b (a i)) =ᵐ[sampleLaw M n]
        fun a => p3_weight M b (W (a i)) := by
  letI := hM.probability
  let f : Fin n → Unit → ℝ := fun j o => if j = i then p3_indicator b o else 1
  let k : Fin n → ℝ → ℝ := fun j w => if j = i then p3_weight M b w else 1
  have h := p3_product_conditional M hM n f k
    (fun j => by
      by_cases hj : j = i
      · simp [f, hj, p3_indicator_measurable b]
      · simp [f, hj])
    (fun j => by
      by_cases hj : j = i
      · simp [k, hj]
        cases b
        · exact measurable_const.sub (hM.measurable_pi.mul hM.measurable_m)
        · exact hM.measurable_pi.mul hM.measurable_m
      · simp [k, hj])
    (fun j => by
      by_cases hj : j = i
      · subst j
        simpa [f] using p3_indicator_integrable M hM b
      · simp [f, hj])
    (fun j => by
      by_cases hj : j = i
      · subst j
        simpa [f, k] using p3_single_conditional M hM b
      · simp [f, k, hj]
        filter_upwards [] with o
        rw [condExp_const (μ := M.law) (m := covariateSigma)
          measurable_fst.comap_le (1 : ℝ)]
        )
  simpa [f, k] using h

private def rangeValue (M : Study) (n : ℕ) (i : Fin n) (a : Sample n) : ℝ :=
  1 / ((n : ℝ) * M.pi (W (a i)))

private def bitCoefficient (M : Study) {n : ℕ} (S : Finset (Fin n))
    (sets : Fin n → Set ℝ) (i : Fin n) (b : Bool) (a : Sample n) : ℝ :=
  if i ∈ S then
    if (if b then rangeValue M n i a else 0) ∈ sets i then 1 else 0
  else 1

private def coefficientProduct (M : Study) {n : ℕ} (S : Finset (Fin n))
    (sets : Fin n → Set ℝ) (b : Fin n → Bool) (a : Sample n) : ℝ :=
  ∏ i, bitCoefficient M S sets i (b i) a

private def indicatorProduct (n : ℕ) (b : Fin n → Bool) (a : Sample n) : ℝ :=
  ∏ i, AronowAudit.P046.Wave1.p3_indicator (b i) (a i)

private lemma bitCoefficient_measurable (M : Study) (hM : ValidStudy M) {n : ℕ}
    (S : Finset (Fin n)) (sets : Fin n → Set ℝ)
    (hsets : ∀ i, i ∈ S → MeasurableSet (sets i)) (i : Fin n) (b : Bool) :
    Measurable[sampleCovariateSigma n] (fun a : Sample n =>
      bitCoefficient M S sets i b a) := by
  classical
  letI : MeasurableSpace (Sample n) := sampleCovariateSigma n
  by_cases hi : i ∈ S
  · cases b
    · simp only [bitCoefficient, if_pos hi, Bool.false_eq_true, if_false]
      exact measurable_const
    · have mr : Measurable[sampleCovariateSigma n]
        (fun a : Sample n => rangeValue M n i a) := by
          unfold rangeValue
          have mw0 : Measurable (fun w : Fin n → ℝ => w i) := measurable_pi_apply i
          have mw : Measurable[sampleCovariateSigma n] (fun a : Sample n => W (a i)) := by
            change Measurable[sampleCovariateSigma n]
              (fun a : Sample n => (fun w : Fin n → ℝ => w i) (covariates a))
            exact mw0.comp (comap_measurable (covariates (n := n)))
          exact measurable_const.div (measurable_const.mul (hM.measurable_pi.comp mw))
      simp only [bitCoefficient, if_pos hi, if_true]
      exact measurable_const.ite (MeasurableSet.preimage (hsets i hi) mr) measurable_const
  · simp [bitCoefficient, hi]

private lemma coefficientProduct_measurable (M : Study) (hM : ValidStudy M) {n : ℕ}
    (S : Finset (Fin n)) (sets : Fin n → Set ℝ)
    (hsets : ∀ i, i ∈ S → MeasurableSet (sets i)) (b : Fin n → Bool) :
    Measurable[sampleCovariateSigma n]
      (coefficientProduct M S sets b) := by
  unfold coefficientProduct
  exact Finset.measurable_prod Finset.univ
    (fun i _ => bitCoefficient_measurable M hM S sets hsets i (b i))

private lemma coefficientProduct_integrable (M : Study) (hM : ValidStudy M) {n : ℕ}
    (S : Finset (Fin n)) (sets : Fin n → Set ℝ)
    (hsets : ∀ i, i ∈ S → MeasurableSet (sets i)) (b : Fin n → Bool) :
    Integrable (fun a => coefficientProduct M S sets b a * indicatorProduct n b a)
      (sampleLaw M n) := by
  letI := hM.probability
  have hle : sampleCovariateSigma n ≤ (inferInstance : MeasurableSpace (Sample n)) := by
    have mc : Measurable (covariates (n := n)) :=
      measurable_pi_lambda (fun j => measurable_fst.comp (measurable_pi_apply j))
    exact mc.comap_le
  have mJ : Measurable (indicatorProduct n b) :=
    Finset.measurable_prod Finset.univ (fun i _ =>
      (p3_indicator_measurable (b i)).comp (measurable_pi_apply i))
  have mCJ : Measurable (fun a : Sample n =>
      coefficientProduct M S sets b a * indicatorProduct n b a) :=
    ((coefficientProduct_measurable M hM S sets hsets b).mono hle le_rfl).mul mJ
  apply memLp_one_iff_integrable.1
    (memLp_of_bounded (a := 0) (b := 1) _
      mCJ.aestronglyMeasurable 1)
  exact ae_of_all _ (fun a => by
    have hfactor (i : Fin n) : bitCoefficient M S sets i (b i) a ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [bitCoefficient]
      split_ifs <;> norm_num
    have hC : coefficientProduct M S sets b a ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [coefficientProduct]
      constructor
      · exact Finset.prod_nonneg (fun i hi => (hfactor i).1)
      · exact Finset.prod_le_one₀
          (fun i hi => (hfactor i).1) (fun i hi => (hfactor i).2)
    have hJ : indicatorProduct n b a =
        if (fun i => (a i).2.1 && (a i).2.2.2) = b then (1 : ℝ) else 0 :=
      p3_product_indicator n b a
    rw [hJ]
    by_cases hb : (fun i => (a i).2.1 && (a i).2.2.2) = b
    · simpa [hb, coefficientProduct] using hC
    · simp [hb])

private lemma indicatorExpansion (M : Study) {n : ℕ} (S : Finset (Fin n))
    (sets : Fin n → Set ℝ) (a : Sample n) :
    (∏ i ∈ S, (if wholeSummand M i a ∈ sets i then (1 : ℝ) else 0)) =
      ∑ b : Fin n → Bool,
        coefficientProduct M S sets b a * indicatorProduct n b a := by
  classical
  have hcoord (i : Fin n) :
      (∑ b : Bool, bitCoefficient M S sets i b a * p3_indicator b (a i)) =
        if i ∈ S then (if wholeSummand M i a ∈ sets i then 1 else 0) else 1 := by
    by_cases hi : i ∈ S
    · cases hb : ((a i).2.1 && (a i).2.2.2) <;>
        simp [bitCoefficient, hi, p3_indicator, AronowAudit.P046.Wave1.p3_indicator,
          wholeSummand_binary, rangeValue, hb]
    · cases hb : ((a i).2.1 && (a i).2.2.2) <;>
        simp [bitCoefficient, hi, p3_indicator, AronowAudit.P046.Wave1.p3_indicator, hb]
  have hp : (∏ i, (∑ b : Bool,
        bitCoefficient M S sets i b a * p3_indicator b (a i))) =
      (∏ i ∈ S, (if wholeSummand M i a ∈ sets i then (1 : ℝ) else 0)) := by
    calc
      _ = ∏ i, if i ∈ S then
          (if wholeSummand M i a ∈ sets i then (1 : ℝ) else 0) else 1 := by
            apply Finset.prod_congr rfl
            intro i hi
            exact hcoord i
      _ = ∏ i ∈ S, (if wholeSummand M i a ∈ sets i then (1 : ℝ) else 0) :=
        Fintype.prod_ite_mem S
          (fun i => if wholeSummand M i a ∈ sets i then (1 : ℝ) else 0)
  calc
    _ = ∏ i, (∑ b : Bool,
          bitCoefficient M S sets i b a * p3_indicator b (a i)) := hp.symm
    _ = ∑ b : Fin n → Bool,
          ∏ i, (bitCoefficient M S sets i (b i) a * p3_indicator (b i) (a i)) :=
      Fintype.prod_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      simp only [Finset.prod_mul_distrib]
      rfl

private lemma conditionalIntersection_expansion (M : Study) (hM : ValidStudy M)
    {n : ℕ} (S : Finset (Fin n)) (sets : Fin n → Set ℝ)
    (hsets : ∀ i, i ∈ S → MeasurableSet (sets i)) :
    condExp (sampleCovariateSigma n) (sampleLaw M n)
      (Set.indicator (⋂ i ∈ S, (wholeSummand M i) ⁻¹' sets i) (fun _ => (1 : ℝ)))
      =ᵐ[sampleLaw M n] fun a =>
        ∑ b : Fin n → Bool,
          coefficientProduct M S sets b a *
            ∏ i, p3_weight M (b i) (W (a i)) := by
  classical
  letI := hM.probability
  let P := sampleLaw M n
  let J (b : Fin n → Bool) (a : Sample n) := indicatorProduct n b a
  let C (b : Fin n → Bool) (a : Sample n) := coefficientProduct M S sets b a
  have hle : sampleCovariateSigma n ≤ (inferInstance : MeasurableSpace (Sample n)) := by
    have mc : Measurable (covariates (n := n)) :=
      measurable_pi_lambda (fun j => measurable_fst.comp (measurable_pi_apply j))
    exact mc.comap_le
  have iJ (b : Fin n → Bool) : Integrable (J b) P :=
    Integrable.fintype_prod (fun i => p3_indicator_integrable M hM (b i))
  have iCJ (b : Fin n → Bool) : Integrable (fun a => C b a * J b a) P := by
    simpa [C, J] using coefficientProduct_integrable M hM S sets hsets b
  have hJ (b : Fin n → Bool) :
      condExp (sampleCovariateSigma n) P (J b) =ᵐ[P] fun a => ∏ i, p3_weight M (b i) (W (a i)) := by
    simpa [P, J, indicatorProduct] using
      (p3_product_conditional M hM n
        (fun i => p3_indicator (b i)) (fun i => p3_weight M (b i))
        (fun i => p3_indicator_measurable (b i))
        (fun i => by
          cases b i
          · change Measurable (fun w : ℝ => 1 - M.pi w * M.m w)
            exact measurable_const.sub (hM.measurable_pi.mul hM.measurable_m)
          · change Measurable (fun w : ℝ => M.pi w * M.m w)
            exact hM.measurable_pi.mul hM.measurable_m)
        (fun i => p3_indicator_integrable M hM (b i))
        (fun i => p3_single_conditional M hM (b i)))
  have hpull (b : Fin n → Bool) :
      condExp (sampleCovariateSigma n) P (fun a => C b a * J b a) =ᵐ[P]
        fun a => C b a * ∏ i, p3_weight M (b i) (W (a i)) := by
    have h := condExp_mul_of_stronglyMeasurable_left
      (coefficientProduct_measurable M hM S sets hsets b).stronglyMeasurable
      (iCJ b) (iJ b)
    exact h.trans ((hJ b).mono fun a ha => congrArg (fun x => C b a * x) ha)
  have hsum := condExp_finsetSum (μ := P)
    (fun b (_ : b ∈ (Finset.univ : Finset (Fin n → Bool))) => iCJ b)
    (sampleCovariateSigma n)
  simp only [Finset.sum_fn] at hsum
  have hpullall := ae_all_iff.2 hpull
  have heq : Set.indicator (⋂ i ∈ S, (wholeSummand M i) ⁻¹' sets i)
      (fun _ => (1 : ℝ)) = fun a =>
        ∑ b : Fin n → Bool, C b a * J b a := by
    funext a
    simp only [Set.indicator_apply, Set.mem_iInter, Set.mem_preimage]
    have hprod :
        (if ∀ i ∈ S, wholeSummand M i a ∈ sets i then (1 : ℝ) else 0) =
          ∏ i ∈ S, (if wholeSummand M i a ∈ sets i then (1 : ℝ) else 0) := by
      classical
      by_cases h : ∀ i ∈ S, wholeSummand M i a ∈ sets i
      · rw [if_pos h]
        have hp : (∏ i ∈ S,
            (if wholeSummand M i a ∈ sets i then (1 : ℝ) else 0)) = 1 := by
          calc
            _ = ∏ i ∈ S, (1 : ℝ) := by
              apply Finset.prod_congr rfl
              intro i hi
              simp [h i hi]
            _ = 1 := by simp
        exact hp.symm
      · push_neg at h
        obtain ⟨i, hi, hnot⟩ := h
        rw [if_neg (by push_neg; exact ⟨i, hi, hnot⟩)]
        exact (Finset.prod_eq_zero hi (by simp [hnot])).symm
    rw [hprod, indicatorExpansion M S sets a]
  filter_upwards [hsum, hpullall] with a hs hp
  rw [heq]
  exact hs.trans (Finset.sum_congr rfl (fun b _ => hp b))

private lemma conditionalSingle_expansion (M : Study) (hM : ValidStudy M)
    {n : ℕ} (S : Finset (Fin n)) (sets : Fin n → Set ℝ)
    (hsets : ∀ i, i ∈ S → MeasurableSet (sets i)) (i : Fin n) (hi : i ∈ S) :
    condExp (sampleCovariateSigma n) (sampleLaw M n)
      (Set.indicator ((wholeSummand M i) ⁻¹' sets i) (fun _ => (1 : ℝ)))
      =ᵐ[sampleLaw M n] fun a =>
        ∑ b : Bool,
          bitCoefficient M S sets i b a * p3_weight M b (W (a i)) := by
  classical
  letI := hM.probability
  let P := sampleLaw M n
  have hle : sampleCovariateSigma n ≤ (inferInstance : MeasurableSpace (Sample n)) := by
    have mc : Measurable (covariates (n := n)) :=
      measurable_pi_lambda (fun j => measurable_fst.comp (measurable_pi_apply j))
    exact mc.comap_le
  have hcoord b := p3_coordinate_conditional M hM i b
  have hcoeff b : Measurable[sampleCovariateSigma n]
      (fun a : Sample n => bitCoefficient M S sets i b a) :=
    bitCoefficient_measurable M hM S sets hsets i b
  have iterm b : Integrable
      (fun a : Sample n => bitCoefficient M S sets i b a * p3_indicator b (a i)) P := by
    letI := hM.probability
    have mI : Measurable (fun a : Sample n => p3_indicator b (a i)) := by
      exact (p3_indicator_measurable b).comp (measurable_pi_apply i)
    have mterm : Measurable (fun a : Sample n =>
        bitCoefficient M S sets i b a * p3_indicator b (a i)) :=
      ((hcoeff b).mono hle le_rfl).mul mI
    apply memLp_one_iff_integrable.1
      (memLp_of_bounded (a := 0) (b := 1) _ mterm.aestronglyMeasurable 1)
    exact ae_of_all _ (fun a => by
      simp [bitCoefficient, p3_indicator, AronowAudit.P046.Wave1.p3_indicator]
      split_ifs <;> norm_num)
  have hpull b :
      condExp (sampleCovariateSigma n) P
        (fun a => bitCoefficient M S sets i b a * p3_indicator b (a i))
        =ᵐ[P] fun a => bitCoefficient M S sets i b a * p3_weight M b (W (a i)) := by
    have hp := condExp_mul_of_stronglyMeasurable_left
      (hcoeff b).stronglyMeasurable (iterm b)
      ((measurePreserving_eval (fun _ : Fin n => M.law) i).integrable_comp_of_integrable
        (p3_indicator_integrable M hM b))
    exact hp.trans ((hcoord b).mono fun a ha =>
      congrArg (fun x => bitCoefficient M S sets i b a * x) ha)
  have heq : Set.indicator ((wholeSummand M i) ⁻¹' sets i) (fun _ => (1 : ℝ)) =
      fun a => ∑ b : Bool,
        bitCoefficient M S sets i b a * p3_indicator b (a i) := by
    funext a
    cases hb : ((a i).2.1 && (a i).2.2.2) <;>
      simp [Set.indicator_apply, bitCoefficient, hi, p3_indicator,
        AronowAudit.P046.Wave1.p3_indicator, wholeSummand_binary, rangeValue, hb]
  have hsum := condExp_finsetSum (μ := P)
    (s := Finset.univ) (fun b _ => iterm b) (sampleCovariateSigma n)
  simp only [Finset.sum_fn] at hsum
  have hpullall := ae_all_iff.2 hpull
  filter_upwards [hsum, hpullall] with a hs hp
  rw [heq]
  exact hs.trans (Finset.sum_congr rfl (fun b _ => hp b))

private lemma conditional_independence (M : Study) (hM : ValidStudy M) (n : ℕ)
    [IsFiniteMeasure (sampleLaw M n)] :
    ∃ hle : sampleCovariateSigma n ≤ (inferInstance : MeasurableSpace (Sample n)),
      iCondIndepFun (sampleCovariateSigma n) hle
        (fun i => wholeSummand M (n := n) i) (sampleLaw M n) := by
  classical
  letI := hM.probability
  let f : ∀ i : Fin n, Sample n → ℝ := fun i => wholeSummand M i
  have hf : ∀ i, Measurable (f i) := fun i => wholeSummand_measurable M hM i
  let P := sampleLaw M n
  have hle : sampleCovariateSigma n ≤ (inferInstance : MeasurableSpace (Sample n)) := by
    have mc : Measurable (covariates (n := n)) :=
      measurable_pi_lambda (fun j => measurable_fst.comp (measurable_pi_apply j))
    exact mc.comap_le
  refine ⟨hle, ?_⟩
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul (fun _ => inferInstance) f hf]
  intro S sets hsets
  let hsets' : ∀ i, i ∈ S → MeasurableSet (sets i) := hsets
  have hmain := conditionalIntersection_expansion M hM S sets hsets'
  have hsingle (i : Fin n) (hi : i ∈ S) :=
    conditionalSingle_expansion M hM S sets hsets' i hi
  have hfinite : ∀ᵐ a ∂sampleLaw M n, ∀ i, i ∈ S →
      (sampleLaw M n⟦(wholeSummand M i) ⁻¹' sets i | sampleCovariateSigma n⟧) a =
        ∑ b : Bool, bitCoefficient M S sets i b a * p3_weight M b (W (a i)) := by
    apply ae_all_iff.2
    intro i
    by_cases hi : i ∈ S
    · filter_upwards [hsingle i hi] with a ha
      intro _
      exact ha
    · filter_upwards [] with a ha
      exact (hi ha).elim
  filter_upwards [hmain, hfinite] with a hmain hsingle
  rw [hmain]
  have hp : (∏ i ∈ S,
      ∑ b : Bool, bitCoefficient M S sets i b a * p3_weight M b (W (a i))) =
      ∑ b : Fin n → Bool,
        coefficientProduct M S sets b a * ∏ i, p3_weight M (b i) (W (a i)) := by
    classical
    have hfactor (i : Fin n) :
        (∑ b : Bool, bitCoefficient M S sets i b a * p3_weight M b (W (a i))) =
          if i ∈ S then
            (∑ b : Bool, bitCoefficient M S sets i b a * p3_weight M b (W (a i)))
          else 1 := by
      by_cases hi : i ∈ S
      · simp [hi]
      · simp only [bitCoefficient, if_neg hi, Fintype.sum_bool, one_mul]
        linarith [p3_weight_sum M (W (a i))]
    have hprod : (∏ i, (∑ b : Bool,
          bitCoefficient M S sets i b a * p3_weight M b (W (a i)))) =
        (∏ i ∈ S, ∑ b : Bool,
          bitCoefficient M S sets i b a * p3_weight M b (W (a i))) := by
      calc
        _ = ∏ i, if i ∈ S then
            (∑ b : Bool, bitCoefficient M S sets i b a * p3_weight M b (W (a i)))
            else 1 := by
              apply Finset.prod_congr rfl
              intro i hi
              exact hfactor i
        _ = ∏ i ∈ S, ∑ b : Bool,
            bitCoefficient M S sets i b a * p3_weight M b (W (a i)) :=
          Fintype.prod_ite_mem S
            (fun i => ∑ b : Bool,
              bitCoefficient M S sets i b a * p3_weight M b (W (a i)))
    rw [← hprod, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro b hb
    simp [coefficientProduct, Finset.prod_mul_distrib]
  have hleft :
      (∏ i ∈ S, (P⟦(f i) ⁻¹' sets i | sampleCovariateSigma n⟧) a) =
        ∏ i ∈ S, (∑ b : Bool,
          bitCoefficient M S sets i b a * p3_weight M b (W (a i))) := by
    apply Finset.prod_congr rfl
    intro i hi
    have h := hsingle i hi
    simpa [P, f] using h
  rw [Finset.prod_apply]
  exact (hleft.trans hp).symm

end

end SAP.P046.WH.W1.P.T3_L2

open SAP.P046.WH.W1.P.T3_L2

theorem SAP.P046.WH.W1.T3_L2_proof : SAP.P046.WH.W1.T3_L2 := by
  classical
  intro M hM n hn
  letI := hM.probability
  letI := sampleLaw_probability M n
  refine ⟨conditional_independence M hM n, ?_⟩
  have hgood := AronowAudit.P046.Wave1.conditional_hoeffding_good
    (Bridge.toStudy M) (Bridge.valid_to hM) n
  filter_upwards [hgood] with a ha
  have hp (i : Fin n) : 0 < M.pi (W (a i)) := lt_trans hM.delta_pos (ha i).1
  have hrec (i : Fin n) : 0 < (M.pi (W (a i)))⁻¹ ^ 2 := by
    exact sq_pos_of_pos (inv_pos.mpr (hp i))
  have hsum : 0 < ∑ i, (M.pi (W (a i)))⁻¹ ^ 2 := by
    apply Finset.sum_pos'
    · intro i hi
      exact (hrec i).le
    · exact ⟨⟨0, hn⟩, by simp, hrec ⟨0, hn⟩⟩
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hxi : 0 < xi M a := by
    unfold xi
    exact div_pos hsum hnR
  have hdenom : wholeDenom M a = xi M a / n := by
    have hfac (i : Fin n) :
        ((n : ℝ) * M.pi (W (a i)))⁻¹ ^ 2 =
          (n : ℝ)⁻¹ ^ 2 * (M.pi (W (a i)))⁻¹ ^ 2 := by
      rw [mul_inv_rev, mul_pow]
      ring
    unfold wholeDenom xi
    simp_rw [hfac]
    rw [← Finset.mul_sum]
    simp [div_eq_mul_inv]
    ring
  have hsqrt := AronowAudit.P046.sqrt_mean_inverse_sq_lt n hn M.delta hM.delta_pos
    (fun i => M.pi (W (a i))) (fun i => (ha i).1)
  refine ⟨?_, ?_, ?_, hdenom, hsqrt⟩
  · intro i
    have hsumd :
        wholeSummand M i a =
          (if (a i).2.1 && (a i).2.2.2 then (1 : ℝ) else 0) /
            ((n : ℝ) * M.pi (W (a i))) := wholeSummand_binary M n i a
    rw [hsumd]
    have hd : 0 < (n : ℝ) * M.pi (W (a i)) := mul_pos hnR (hp i)
    constructor
    · by_cases hb : (a i).2.1 && (a i).2.2.2
      · rw [if_pos hb]
        exact (div_pos one_pos hd).le
      · rw [if_neg hb]
        simp
    · rw [show ((n : ℝ) * M.pi (W (a i)))⁻¹ =
        1 / ((n : ℝ) * M.pi (W (a i))) by rw [one_div]]
      by_cases hb : (a i).2.1 && (a i).2.2.2
      · rw [if_pos hb]
      · rw [if_neg hb]
        have hnonneg : 0 ≤ 1 / ((n : ℝ) * M.pi (W (a i))) :=
          div_nonneg (by norm_num) hd.le
        simpa [hb] using hnonneg
  · exact hxi
  · rw [hdenom]
    exact div_pos hxi hnR

