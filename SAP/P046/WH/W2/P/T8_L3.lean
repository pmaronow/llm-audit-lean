import SAP.P046.WH.W2.Leaves
import AronowAudit.P046.Wave1.Gap.GP046B4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P046.WH.W2.P.T8_L3

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

private lemma integrable_bdd01 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hr : ∀ a, 0 ≤ f a ∧ f a ≤ 1) : Integrable f μ := by
  exact memLp_one_iff_integrable.mp
    (memLp_of_bounded (a := 0) (b := 1) (Filter.Eventually.of_forall hr)
      hf.aestronglyMeasurable 1)

private lemma treatment_integrable (M : Study) (hM : ValidStudy M) : Integrable X M.law := by
  letI := hM.probability
  have hx : Measurable X := (measurable_of_countable bit).comp measurable_snd.fst
  apply integrable_bdd01 M.law X hx
  intro o
  rcases o with ⟨w, x, y0, y1⟩
  cases x <;> norm_num [X, bit]

/-- Pull a bounded covariate multiplier through the stored propensity. -/
private lemma integral_covariate_mul_treatment (M : Study) (hM : ValidStudy M)
    (k : ℝ → ℝ) (hk : Measurable k) (hr : ∀ w, 0 ≤ k w ∧ k w ≤ 1) :
    (∫ o, k (W o) * X o ∂M.law) = ∫ o, k (W o) * M.pi (W o) ∂M.law := by
  letI := hM.probability
  have hm : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := by
    change MeasurableSpace.comap (fun o : Unit => o.1) inferInstance ≤ _
    exact Measurable.comap_le (f := fun o : Unit => o.1) measurable_fst
  letI : IsFiniteMeasure (M.law.trim hm) := isFiniteMeasure_trim hm
  have hkS : StronglyMeasurable[covariateSigma] (fun o : Unit => k (W o)) :=
    (hk.comp (comap_measurable W)).stronglyMeasurable
  have hX := treatment_integrable M hM
  have hprod : Integrable (fun o => k (W o) * X o) M.law := by
    apply hX.bdd_mul (hkS.mono hm).aestronglyMeasurable
    filter_upwards [] with o
    rw [Real.norm_eq_abs, abs_of_nonneg (hr (W o)).1]
    exact (hr (W o)).2
  have hpull := condExp_mul_of_stronglyMeasurable_left hkS hprod hX
  have hce : condExp covariateSigma M.law (fun o => k (W o) * X o) =ᵐ[M.law]
      fun o => k (W o) * M.pi (W o) := by
    filter_upwards [hpull, hM.propensity] with o hp hpi
    change condExp covariateSigma M.law ((fun x => k (W x)) * X) o = _
    rw [hp]
    change k (W o) * condExp covariateSigma M.law X o = _
    rw [hpi]
  calc
    _ = ∫ o, (condExp covariateSigma M.law (fun x => k (W x) * X x)) o ∂M.law :=
      (integral_condExp (hm := hm) (f := fun o => k (W o) * X o)).symm
    _ = _ := integral_congr_ae hce

private lemma pi_in_unit_interval (M : Study) (hM : ValidStudy M) :
    ∀ᵐ o ∂M.law, 0 ≤ M.pi (W o) ∧ M.pi (W o) ≤ 1 := by
  filter_upwards [hM.positivity] with o ho
  constructor <;> linarith [hM.delta_pos]

private def eventPropensity (s : Set ℝ) (p : ℝ) : ℝ :=
  (1 - p) * Set.indicator s (fun _ => (1 : ℝ)) 0 +
    p * Set.indicator s (fun _ => (1 : ℝ)) 1

private lemma eventPropensity_bounds (s : Set ℝ) {p : ℝ}
    (hp : 0 ≤ p ∧ p ≤ 1) : 0 ≤ eventPropensity s p ∧ eventPropensity s p ≤ 1 := by
  classical
  have hc0 : 0 ≤ Set.indicator s (fun _ => (1 : ℝ)) 0 ∧
      Set.indicator s (fun _ => (1 : ℝ)) 0 ≤ 1 := by simp [Set.indicator]; split_ifs <;> norm_num
  have hc1 : 0 ≤ Set.indicator s (fun _ => (1 : ℝ)) 1 ∧
      Set.indicator s (fun _ => (1 : ℝ)) 1 ≤ 1 := by simp [Set.indicator]; split_ifs <;> norm_num
  have h1p : 0 ≤ 1 - p := by linarith [hp.2]
  constructor
  · exact add_nonneg (mul_nonneg h1p hc0.1) (mul_nonneg hp.1 hc1.1)
  · calc
      eventPropensity s p ≤ (1-p) * 1 + p * 1 := by
        unfold eventPropensity
        exact add_le_add (mul_le_mul_of_nonneg_left hc0.2 h1p)
          (mul_le_mul_of_nonneg_left hc1.2 hp.1)
      _ = 1 := by ring

private lemma pi_event_prob (M : Study) (hM : ValidStudy M) (s : Set ℝ)
    (k : ℝ → ℝ) (hk : Measurable k) (hr : ∀ w, 0 ≤ k w ∧ k w ≤ 1) :
    (∫ o, k (W o) * Set.indicator (X ⁻¹' s) (fun _ => (1 : ℝ)) o ∂M.law) =
      ∫ o, k (W o) * eventPropensity s (M.pi (W o)) ∂M.law := by
  classical
  letI := hM.probability
  let c0 : ℝ := Set.indicator s (fun _ => (1 : ℝ)) 0
  let c1 : ℝ := Set.indicator s (fun _ => (1 : ℝ)) 1
  have hc0 : 0 ≤ c0 ∧ c0 ≤ 1 := by simp [c0, Set.indicator]; split_ifs <;> norm_num
  have hc1 : 0 ≤ c1 ∧ c1 ≤ 1 := by simp [c1, Set.indicator]; split_ifs <;> norm_num
  have hpoint : Set.indicator (X ⁻¹' s) (fun _ => (1 : ℝ)) =
      fun o => c0 + (c1 - c0) * X o := by
    funext o
    rcases o with ⟨w, x, y0, y1⟩
    cases x <;> simp [Set.indicator, X, bit, c0, c1]
  have hX := integral_covariate_mul_treatment M hM k hk hr
  have hkI : Integrable (fun o : Unit => k (W o)) M.law :=
    integrable_bdd01 M.law (fun o => k (W o)) (hk.comp (by change Measurable (fun o : Unit => o.1); exact measurable_fst)) (fun o => hr (W o))
  have hpiI : Integrable (fun o : Unit => k (W o) * M.pi (W o)) M.law := by
    have hq := pi_in_unit_interval M hM
    have hm : Measurable (fun o : Unit => k (W o) * M.pi (W o)) := by
      exact (hk.comp (by change Measurable (fun o : Unit => o.1); exact measurable_fst)).mul
        (hM.measurable_pi.comp (by change Measurable (fun o : Unit => o.1); exact measurable_fst))
    apply memLp_one_iff_integrable.mp
    apply memLp_of_bounded (a := 0) (b := 1) _ hm.aestronglyMeasurable 1
    filter_upwards [hq] with o ho
    constructor
    · exact mul_nonneg (hr (W o)).1 ho.1
    · calc
        k (W o) * M.pi (W o) ≤ 1 * M.pi (W o) :=
          mul_le_mul_of_nonneg_right (hr (W o)).2 ho.1
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left ho.2 (by norm_num)
        _ = 1 := by ring
  have hprod : Integrable (fun o : Unit => k (W o) *
      (c0 + (c1 - c0) * X o)) M.law := by
    have hf : Measurable (fun o : Unit => k (W o) * (c0 + (c1-c0)*X o)) := by
      exact (hk.comp (by change Measurable (fun o : Unit => o.1); exact measurable_fst)).mul
        (measurable_const.add (measurable_const.mul ((measurable_of_countable bit).comp measurable_snd.fst)))
    apply memLp_one_iff_integrable.mp
    apply memLp_of_bounded (a := 0) (b := 1) _ hf.aestronglyMeasurable 1
    filter_upwards [] with o
    have hx : X o = 0 ∨ X o = 1 := by rcases o with ⟨w,x,y0,y1⟩; cases x <;> simp [X,bit]
    rcases hx with hx | hx
    · have he : c0 + (c1-c0)*X o = c0 := by rw [hx]; ring
      rw [he]
      exact ⟨mul_nonneg (hr (W o)).1 hc0.1,
        (mul_le_mul_of_nonneg_left hc0.2 (hr (W o)).1).trans (by simpa using (hr (W o)).2)⟩
    · have he : c0 + (c1-c0)*X o = c1 := by rw [hx]; ring
      rw [he]
      exact ⟨mul_nonneg (hr (W o)).1 hc1.1,
        (mul_le_mul_of_nonneg_left hc1.2 (hr (W o)).1).trans (by simpa using (hr (W o)).2)⟩
  have hKX : Integrable (fun o : Unit => k (W o) * X o) M.law := by
    apply integrable_bdd01 M.law (fun o => k (W o) * X o) (by
      exact (hk.comp (by change Measurable (fun o : Unit => o.1); exact measurable_fst)).mul
        ((measurable_of_countable bit).comp measurable_snd.fst))
    intro o
    have hx : X o = 0 ∨ X o = 1 := by rcases o with ⟨w,x,y0,y1⟩; cases x <;> simp [X,bit]
    rcases hx with hx | hx
    · rw [hx]
      constructor <;> simp <;> positivity
    · simpa [hx] using hr (W o)
  have hscalar : ∫ o, k (W o) * (c0 + (c1-c0) * X o) ∂M.law =
      c0 * (∫ o, k (W o) ∂M.law) + (c1-c0) * (∫ o, k (W o) * X o ∂M.law) := by
    rw [show (fun o => k (W o) * (c0 + (c1-c0)*X o)) =
      (fun o => c0 * k (W o) + (c1-c0) * (k (W o) * X o)) by funext o; ring]
    rw [integral_add (hkI.const_mul c0) (hKX.const_mul (c1-c0)),
      integral_const_mul, integral_const_mul]
  have hscalar' : ∫ o, k (W o) * (c0 + (c1-c0) * M.pi (W o)) ∂M.law =
      c0 * (∫ o, k (W o) ∂M.law) + (c1-c0) * (∫ o, k (W o) * M.pi (W o) ∂M.law) := by
    rw [show (fun o => k (W o) * (c0 + (c1-c0)*M.pi (W o))) =
      (fun o => c0 * k (W o) + (c1-c0) * (k (W o) * M.pi (W o))) by funext o; ring]
    rw [integral_add (hkI.const_mul c0) (hpiI.const_mul (c1-c0)),
      integral_const_mul, integral_const_mul]
  have hscalar_event : ∫ o, k (W o) * eventPropensity s (M.pi (W o)) ∂M.law =
      c0 * (∫ o, k (W o) ∂M.law) + (c1-c0) * (∫ o, k (W o) * M.pi (W o) ∂M.law) := by
    calc
      _ = ∫ o, k (W o) * (c0 + (c1-c0) * M.pi (W o)) ∂M.law := by
        congr 1
        funext o
        dsimp [eventPropensity, c0, c1]
        ring
      _ = _ := hscalar'
  have hpoint' : (fun o => k (W o) * Set.indicator (X ⁻¹' s) (fun _ => (1 : ℝ)) o) =
      fun o => k (W o) * (c0 + (c1-c0) * X o) := by
    funext o
    rw [hpoint]
  calc
    _ = ∫ o, k (W o) * (c0 + (c1-c0) * X o) ∂M.law := by rw [hpoint']
    _ = c0 * (∫ o, k (W o) ∂M.law) + (c1-c0) *
        (∫ o, k (W o) * X o ∂M.law) := hscalar
    _ = c0 * (∫ o, k (W o) ∂M.law) + (c1-c0) *
        (∫ o, k (W o) * M.pi (W o) ∂M.law) := by rw [hX]
    _ = ∫ o, k (W o) * eventPropensity s (M.pi (W o)) ∂M.law := hscalar_event.symm

private lemma condExp_treatment_event (M : Study) (hM : ValidStudy M) (n : ℕ)
    (i : Fin n) (s : Set ℝ) (hs : MeasurableSet s) :
    (fun a : Sample n => eventPropensity s (M.pi (W (a i)))) =ᵐ[sampleLaw M n]
      condExp (wholeOwnSigma n i) (sampleLaw M n)
        (fun a => Set.indicator ((fun b => X (b i)) ⁻¹' s) (fun _ => (1 : ℝ)) a) := by
  classical
  letI := hM.probability
  let μ := sampleLaw M n
  let full : MeasurableSpace (Sample n) := MeasurableSpace.pi
  letI : MeasurableSpace (Sample n) := full
  let Wi : Sample n → ℝ := fun a => W (a i)
  let A : Sample n → ℝ := fun a => Set.indicator ((fun b => X (b i)) ⁻¹' s)
    (fun _ => (1 : ℝ)) a
  have heval : @Measurable (Sample n) Unit full
      (inferInstance : MeasurableSpace Unit) (fun a => a i) :=
    @measurable_pi_apply (Fin n) (fun _ => Unit)
      (fun _ => (inferInstance : MeasurableSpace Unit)) i
  have hWi : @Measurable (Sample n) ℝ full
      (inferInstance : MeasurableSpace ℝ) Wi := by
    change Measurable (fun a : Sample n => W (a i))
    exact measurable_fst.comp heval
  have hm : wholeOwnSigma n i ≤ full := by
    change MeasurableSpace.comap (fun a : Sample n => W (a i)) inferInstance ≤ _
    exact Measurable.comap_le (f := fun a : Sample n => W (a i)) hWi
  letI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  have hXi : @Measurable (Sample n) ℝ full (inferInstance : MeasurableSpace ℝ)
      (fun a : Sample n => X (a i)) := by
    change Measurable (fun a : Sample n => bit ((a i).2.1))
    exact (measurable_of_countable bit).comp
      ((measurable_snd.fst).comp heval)
  have hAmeas : @Measurable (Sample n) ℝ full (inferInstance : MeasurableSpace ℝ) A := by
    exact measurable_const.indicator (hs.preimage hXi)
  have hAint : Integrable A μ := by
    apply integrable_bdd01 μ A hAmeas
    intro a
    by_cases ha : X (a i) ∈ s <;> simp [A, Set.indicator, ha]
  have hpiAE : ∀ᵐ a ∂μ, 0 ≤ M.pi (W (a i)) ∧ M.pi (W (a i)) ≤ 1 :=
    (measurePreserving_eval (fun _ : Fin n => M.law) i).quasiMeasurePreserving.ae
      (pi_in_unit_interval M hM)
  have hqAE : ∀ᵐ a ∂μ, 0 ≤ eventPropensity s (M.pi (W (a i))) ∧
      eventPropensity s (M.pi (W (a i))) ≤ 1 := by
    filter_upwards [hpiAE] with a ha
    exact eventPropensity_bounds s ha
  have hqMeas : @Measurable (Sample n) ℝ full (inferInstance : MeasurableSpace ℝ)
      (fun a : Sample n => eventPropensity s (M.pi (W (a i)))) := by
    have hp : Measurable (fun a : Sample n => M.pi (W (a i))) :=
      hM.measurable_pi.comp hWi
    have hc0 : Measurable (fun _ : Sample n => Set.indicator s (fun _ => (1 : ℝ)) 0) := measurable_const
    have hc1 : Measurable (fun _ : Sample n => Set.indicator s (fun _ => (1 : ℝ)) 1) := measurable_const
    exact (measurable_const.sub hp).mul hc0 |>.add (hp.mul hc1)
  have hqInt : Integrable (fun a : Sample n => eventPropensity s (M.pi (W (a i)))) μ := by
    apply memLp_one_iff_integrable.mp
    apply memLp_of_bounded (a := 0) (b := 1) hqAE hqMeas.aestronglyMeasurable 1
  have hset : ∀ t : Set ℝ, MeasurableSet t →
      (∫ a in Wi ⁻¹' t, eventPropensity s (M.pi (W (a i))) ∂μ) =
        ∫ a in Wi ⁻¹' t, A a ∂μ := by
    intro t ht
    have hC : MeasurableSet (Wi ⁻¹' t) := ht.preimage hWi
    let k : ℝ → ℝ := Set.indicator t (fun _ => (1 : ℝ))
    have hk : Measurable k := measurable_const.indicator ht
    have hkr : ∀ w, 0 ≤ k w ∧ k w ≤ 1 := by
      intro w
      by_cases hw : w ∈ t <;> simp [k, Set.indicator, hw]
    have hunit : (∫ o, k (W o) * Set.indicator (X ⁻¹' s) (fun _ => (1 : ℝ)) o ∂M.law) =
        ∫ o, k (W o) * eventPropensity s (M.pi (W o)) ∂M.law :=
      pi_event_prob M hM s k hk hkr
    let Aunit : Unit → ℝ := fun o => Set.indicator (X ⁻¹' s) (fun _ => (1 : ℝ)) o
    have hAunit : Measurable Aunit := by
      exact measurable_const.indicator (hs.preimage ((measurable_of_countable bit).comp measurable_snd.fst))
    have hkw : Measurable (fun o : Unit => k (W o)) := hk.comp measurable_fst
    have hqW : Measurable (fun o : Unit => eventPropensity s (M.pi (W o))) := by
      have hw : Measurable W := measurable_fst
      have hp := hM.measurable_pi.comp hw
      exact (measurable_const.sub hp).mul measurable_const |>.add (hp.mul measurable_const)
    have hcand : (∫ a, k (W (a i)) * eventPropensity s (M.pi (W (a i))) ∂μ) =
        ∫ o, k (W o) * eventPropensity s (M.pi (W o)) ∂M.law := by
      simpa [sampleLaw, μ, k] using
        (integral_comp_eval (μ := fun _ : Fin n => M.law) (i := i)
          (f := fun o : Unit => k (W o) * eventPropensity s (M.pi (W o)))
          (hkw.mul hqW).aestronglyMeasurable)
    have hsrc : (∫ a, k (W (a i)) * A a ∂μ) =
        ∫ o, k (W o) * Aunit o ∂M.law := by
      calc
        _ = ∫ a, k (W (a i)) * Aunit (a i) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with a
          rfl
        _ = ∫ o, k (W o) * Aunit o ∂M.law := by
          simpa [sampleLaw, μ, k] using
            (integral_comp_eval (μ := fun _ : Fin n => M.law) (i := i)
              (f := fun o : Unit => k (W o) * Aunit o) (hkw.mul hAunit).aestronglyMeasurable)
    calc
      _ = ∫ a, (Wi ⁻¹' t).indicator
          (fun a => eventPropensity s (M.pi (W (a i)))) a ∂μ :=
        (integral_indicator hC).symm
      _ = ∫ a, (Wi ⁻¹' t).indicator A a ∂μ := by
        calc
          _ = ∫ a, k (W (a i)) * eventPropensity s (M.pi (W (a i))) ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with a
            by_cases ha : a ∈ Wi ⁻¹' t
            · change W (a i) ∈ t at ha
              simp [k, Wi, Set.indicator, ha]
            · change W (a i) ∉ t at ha
              simp [k, Wi, Set.indicator, ha]
          _ = ∫ o, k (W o) * eventPropensity s (M.pi (W o)) ∂M.law := hcand
          _ = ∫ o, k (W o) * Set.indicator (X ⁻¹' s) (fun _ => (1 : ℝ)) o ∂M.law := hunit.symm
          _ = ∫ a, k (W (a i)) * A a ∂μ := hsrc.symm
          _ = ∫ a, (Wi ⁻¹' t).indicator A a ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with a
            by_cases ha : a ∈ Wi ⁻¹' t
            · change W (a i) ∈ t at ha
              simp [k, Wi, A, Set.indicator, ha]
            · change W (a i) ∉ t at ha
              simp [k, Wi, A, Set.indicator, ha]
      _ = _ := integral_indicator hC
  have hqBorel : Measurable (fun w : ℝ => eventPropensity s (M.pi w)) := by
    have hp := hM.measurable_pi
    exact (measurable_const.sub hp).mul measurable_const |>.add (hp.mul measurable_const)
  have hqSM : StronglyMeasurable[wholeOwnSigma n i]
      (fun a : Sample n => eventPropensity s (M.pi (W (a i)))) :=
    (hqBorel.comp (comap_measurable Wi)).stronglyMeasurable
  have hqCE := ae_eq_condExp_of_forall_setIntegral_eq hm hAint
    (fun _ _ _ => hqInt.integrableOn)
    (fun s hs _ => by
      obtain ⟨t, ht, rfl⟩ := hs
      exact hset t ht) hqSM.aestronglyMeasurable
  exact hqCE

private lemma indicator_bdd01 {α : Type*} (s : Set α) (x : α) :
    0 ≤ Set.indicator s (fun _ => (1 : ℝ)) x ∧
      Set.indicator s (fun _ => (1 : ℝ)) x ≤ 1 := by
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

private lemma joint_indicator_factor (M : Study) (hM : ValidStudy M) {n : ℕ}
    (F : CrossFit n) (i : Fin n) (s t u : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u) :
    ∫ a, Set.indicator (fun a : Sample n => W (a i) ∈ u) (fun _ => (1 : ℝ)) a *
        Set.indicator ((fun a : Sample n => X (a i)) ⁻¹' s) (fun _ => (1 : ℝ)) a *
        Set.indicator ((wholePrediction F i) ⁻¹' t) (fun _ => (1 : ℝ)) a ∂sampleLaw M n =
      ∫ a, Set.indicator (fun a : Sample n => W (a i) ∈ u) (fun _ => (1 : ℝ)) a *
        eventPropensity s (M.pi (W (a i))) *
        Set.indicator ((wholePrediction F i) ⁻¹' t) (fun _ => (1 : ℝ)) a ∂sampleLaw M n := by
  classical
  letI := hM.probability
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    let μ := sampleLaw M (m + 1)
    let ν := sampleLaw M m
    let Wi : Sample (m + 1) → ℝ := fun a => W (a i)
    let X_i : Sample (m + 1) → ℝ := fun a => X (a i)
    let P_i : Sample (m + 1) → ℝ := wholePrediction F i
    let A : Sample (m + 1) → ℝ := fun a =>
      Set.indicator (X_i ⁻¹' s) (fun _ => (1 : ℝ)) a
    let B : Sample (m + 1) → ℝ := fun a =>
      Set.indicator (P_i ⁻¹' t) (fun _ => (1 : ℝ)) a
    let C : Sample (m + 1) → ℝ := fun a =>
      Set.indicator (Wi ⁻¹' u) (fun _ => (1 : ℝ)) a
    let Q : Sample (m + 1) → ℝ := fun a => eventPropensity s (M.pi (Wi a))
    let f : Sample (m + 1) → ℝ := fun a => C a * A a * B a
    let g : Sample (m + 1) → ℝ := fun a => C a * Q a * B a
    have heval : @Measurable (Sample (m + 1)) Unit MeasurableSpace.pi
        (inferInstance : MeasurableSpace Unit) (fun a => a i) :=
      @measurable_pi_apply (Fin (m + 1)) (fun _ => Unit)
        (fun _ => (inferInstance : MeasurableSpace Unit)) i
    have hWi : @Measurable (Sample (m + 1)) ℝ MeasurableSpace.pi
        (inferInstance : MeasurableSpace ℝ) Wi := by
      change Measurable (fun a : Sample (m + 1) => W (a i))
      exact measurable_fst.comp heval
    have hXi : @Measurable (Sample (m + 1)) ℝ MeasurableSpace.pi
        (inferInstance : MeasurableSpace ℝ) X_i := by
      change Measurable (fun a : Sample (m + 1) => bit ((a i).2.1))
      exact (measurable_of_countable bit).comp ((measurable_snd.fst).comp heval)
    have hPi : Measurable P_i := by
      dsimp [P_i, wholePrediction]
      exact (F.measurable_g (F.fold i)).comp
        (measurable_id.prodMk (measurable_fst.comp heval))
    have hAm : @Measurable (Sample (m + 1)) ℝ MeasurableSpace.pi
        (inferInstance : MeasurableSpace ℝ) A := by
      exact measurable_const.indicator (hs.preimage hXi)
    have hBm : @Measurable (Sample (m + 1)) ℝ MeasurableSpace.pi
        (inferInstance : MeasurableSpace ℝ) B :=
      measurable_const.indicator (ht.preimage hPi)
    have hCm : @Measurable (Sample (m + 1)) ℝ MeasurableSpace.pi
        (inferInstance : MeasurableSpace ℝ) C :=
      measurable_const.indicator (hu.preimage hWi)
    have hQm : @Measurable (Sample (m + 1)) ℝ MeasurableSpace.pi
        (inferInstance : MeasurableSpace ℝ) Q := by
      dsimp [Q, Wi]
      exact (measurable_const.sub (hM.measurable_pi.comp hWi)).mul measurable_const |>.add
        ((hM.measurable_pi.comp hWi).mul measurable_const)
    have hfm : Measurable f := by dsimp [f]; exact hCm.mul hAm |>.mul hBm
    have hgm : Measurable g := by dsimp [g]; exact hCm.mul hQm |>.mul hBm
    have hfI : Integrable f μ := by
      apply integrable_bdd01 μ f hfm
      intro a
      have hC' := indicator_bdd01 (Wi ⁻¹' u) a
      have hA' := indicator_bdd01 (X_i ⁻¹' s) a
      have hB' := indicator_bdd01 (P_i ⁻¹' t) a
      dsimp [f, C, A, B]
      constructor
      · exact mul_nonneg (mul_nonneg hC'.1 hA'.1) hB'.1
      · calc
          _ ≤ C a * B a := mul_le_mul_of_nonneg_right
            (calc C a * A a ≤ C a * 1 := mul_le_mul_of_nonneg_left hA'.2 hC'.1
                  _ = C a := by ring) hB'.1
          _ ≤ 1 * B a := mul_le_mul_of_nonneg_right hC'.2 hB'.1
          _ ≤ 1 := by simpa using hB'.2
    have hpEval := measurePreserving_eval (fun _ : Fin (m + 1) => M.law) i
    have hpiAE : ∀ᵐ a ∂μ, 0 ≤ M.pi (Wi a) ∧ M.pi (Wi a) ≤ 1 := by
      have hpos := hpEval.quasiMeasurePreserving.ae hM.positivity
      filter_upwards [hpos] with a ha
      constructor <;> dsimp [Wi] <;> linarith [hM.delta_pos]
    have hqAE : ∀ᵐ a ∂μ, 0 ≤ Q a ∧ Q a ≤ 1 := by
      filter_upwards [hpiAE] with a ha
      exact eventPropensity_bounds s ha
    have hgI : Integrable g μ := by
      have hgB : ∀ᵐ a ∂μ, 0 ≤ g a ∧ g a ≤ 1 := by
        filter_upwards [hqAE] with a hq
        have hC' := indicator_bdd01 (Wi ⁻¹' u) a
        have hB' := indicator_bdd01 (P_i ⁻¹' t) a
        dsimp [g, C, B, Q]
        constructor
        · exact mul_nonneg (mul_nonneg hC'.1 hq.1) hB'.1
        · calc
            _ ≤ C a * B a := mul_le_mul_of_nonneg_right
              (calc C a * Q a ≤ C a * 1 := mul_le_mul_of_nonneg_left hq.2 hC'.1
                    _ = C a := by ring) hB'.1
            _ ≤ 1 * B a := mul_le_mul_of_nonneg_right hC'.2 hB'.1
            _ ≤ 1 := by simpa using hB'.2
      apply memLp_one_iff_integrable.mp
      exact memLp_of_bounded (a := 0) (b := 1) hgB hgm.aestronglyMeasurable 1
    have hpres :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => M.law) i).symm
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Unit) i
    let o₀ : Unit := (0, (false, (false, false)))
    let frozen (r : Sample m) (w : ℝ) : ℝ :=
      F.g (F.fold i) (i.insertNth o₀ r) w
    have hfit (o : Unit) (r : Sample m) :
        F.g (F.fold i) (i.insertNth o r) = F.g (F.fold i) (i.insertNth o₀ r) :=
      AronowAudit.P046.Wave1.proposition4a_fit_insert (SAP.P046.Bridge.toFit F) i r o o₀
    have hpred (o : Unit) (r : Sample m) :
        wholePrediction F i (i.insertNth o r) = frozen r (W o) := by
      dsimp [P_i, wholePrediction, frozen]
      rw [hfit o r, Fin.insertNth_apply_same]
    let P : Unit × Sample m → ℝ := fun z =>
      Set.indicator u (fun _ => (1 : ℝ)) (W z.1) *
        Set.indicator (X ⁻¹' s) (fun _ => (1 : ℝ)) z.1 *
        Set.indicator {o | frozen z.2 (W o) ∈ t} (fun _ => (1 : ℝ)) z.1
    let R : Unit × Sample m → ℝ := fun z =>
      Set.indicator u (fun _ => (1 : ℝ)) (W z.1) *
        eventPropensity s (M.pi (W z.1)) *
        Set.indicator {o | frozen z.2 (W o) ∈ t} (fun _ => (1 : ℝ)) z.1
    have hfe : (fun z : Unit × Sample m => f (e.symm z)) = P := by
      funext z
      rcases z with ⟨o, r⟩
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk]
      change C (i.insertNth o r) * A (i.insertNth o r) * B (i.insertNth o r) = P (o, r)
      have hCpoint : C (i.insertNth o r) = Set.indicator u (fun _ => (1 : ℝ)) (W o) := by
        dsimp [C, Wi]
        simp only [Set.indicator, Set.mem_preimage]
        rw [Fin.insertNth_apply_same]
      have hApoint : A (i.insertNth o r) =
          Set.indicator (X ⁻¹' s) (fun _ => (1 : ℝ)) o := by
        dsimp [A, X_i]
        simp only [Set.indicator, Set.mem_preimage]
        rw [Fin.insertNth_apply_same]
      have hBpoint : B (i.insertNth o r) =
          Set.indicator {o | frozen r (W o) ∈ t} (fun _ => (1 : ℝ)) o := by
        simp [B, P_i, Set.indicator, hpred o r]
      rw [hCpoint, hApoint, hBpoint]
    have hge : (fun z : Unit × Sample m => g (e.symm z)) = R := by
      funext z
      rcases z with ⟨o, r⟩
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk]
      change C (i.insertNth o r) * Q (i.insertNth o r) * B (i.insertNth o r) = R (o, r)
      have hCpoint : C (i.insertNth o r) = Set.indicator u (fun _ => (1 : ℝ)) (W o) := by
        dsimp [C, Wi]
        simp only [Set.indicator, Set.mem_preimage]
        rw [Fin.insertNth_apply_same]
      have hQpoint : Q (i.insertNth o r) = eventPropensity s (M.pi (W o)) := by
        simp [Q, Wi, Fin.insertNth_apply_same]
      have hBpoint : B (i.insertNth o r) =
          Set.indicator {o | frozen r (W o) ∈ t} (fun _ => (1 : ℝ)) o := by
        simp [B, P_i, Set.indicator, hpred o r]
      rw [hCpoint, hQpoint, hBpoint]
    have hprodF : Integrable (fun z : Unit × Sample m => f (e.symm z))
        (M.law.prod ν) := by
      simpa [e, ν, sampleLaw, Function.comp_def] using hpres.integrable_comp_of_integrable hfI
    have hprodG : Integrable (fun z : Unit × Sample m => g (e.symm z))
        (M.law.prod ν) := by
      simpa [e, ν, sampleLaw, Function.comp_def] using hpres.integrable_comp_of_integrable hgI
    have hPint : Integrable P (M.law.prod ν) := by simpa only [hfe] using hprodF
    have hRint : Integrable R (M.law.prod ν) := by simpa only [hge] using hprodG
    have hinner (r : Sample m) :
        (∫ o, P (o, r) ∂M.law) = ∫ o, R (o, r) ∂M.law := by
      let k : ℝ → ℝ := fun w => Set.indicator u (fun _ => (1 : ℝ)) w *
        Set.indicator {w | frozen r w ∈ t} (fun _ => (1 : ℝ)) w
      have hfr : Measurable (frozen r) := by
        dsimp [frozen]
        exact (F.measurable_g (F.fold i)).comp (measurable_const.prodMk measurable_id)
      have hk : Measurable k := by
        dsimp [k]
        exact (measurable_const.indicator hu).mul
          (measurable_const.indicator (ht.preimage hfr))
      have hkr : ∀ w, 0 ≤ k w ∧ k w ≤ 1 := by
        intro w
        have hu' := indicator_bdd01 u w
        have ht' := indicator_bdd01 {w | frozen r w ∈ t} w
        dsimp [k]
        constructor
        · exact mul_nonneg hu'.1 ht'.1
        · calc
            _ ≤ 1 * Set.indicator {w | frozen r w ∈ t} (fun _ => (1 : ℝ)) w :=
              mul_le_mul_of_nonneg_right hu'.2 ht'.1
            _ ≤ 1 := by simpa using ht'.2
      calc
        _ = ∫ o, k (W o) * Set.indicator (X ⁻¹' s) (fun _ => (1 : ℝ)) o ∂M.law := by
          apply integral_congr_ae
          filter_upwards [] with o
          by_cases hu' : W o ∈ u <;> by_cases hs' : X o ∈ s <;>
            by_cases ht' : frozen r (W o) ∈ t <;> simp [P, k, Set.indicator, hu', hs', ht']
        _ = ∫ o, k (W o) * eventPropensity s (M.pi (W o)) ∂M.law :=
          pi_event_prob M hM s k hk hkr
        _ = ∫ o, R (o, r) ∂M.law := by
          apply integral_congr_ae
          filter_upwards [] with o
          by_cases hu' : W o ∈ u <;> by_cases ht' : frozen r (W o) ∈ t <;>
            simp [R, k, Set.indicator, hu', ht']
    have hprodEq : (∫ z, P z ∂M.law.prod ν) = ∫ z, R z ∂M.law.prod ν := by
      rw [integral_prod_symm P hPint, integral_prod_symm R hRint]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hinner
    have hsourceF : (∫ a, f a ∂μ) = ∫ z, P z ∂M.law.prod ν := by
      calc
        _ = ∫ z, f (e.symm z) ∂M.law.prod ν := by
          simpa [μ, ν, sampleLaw, e, Function.comp_def] using (hpres.integral_comp' f).symm
        _ = _ := by rw [hfe]
    have hsourceG : (∫ a, g a ∂μ) = ∫ z, R z ∂M.law.prod ν := by
      calc
        _ = ∫ z, g (e.symm z) ∂M.law.prod ν := by
          simpa [μ, ν, sampleLaw, e, Function.comp_def] using (hpres.integral_comp' g).symm
        _ = _ := by rw [hge]
    convert hsourceF.trans (hprodEq.trans hsourceG.symm) using 1 <;>
      congr 1 <;> funext a <;> rfl

end

end SAP.P046.WH.W2.P.T8_L3

open SAP.P046.WH.W2.P.T8_L3
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal

theorem SAP.P046.WH.W2.T8_L3_proof : SAP.P046.WH.W2.T8_L3 := by
  intro M hM n F i
  unfold SAP.P046.wholeFitIndependent
  letI := hM.probability
  let μ := sampleLaw M n
  let full : MeasurableSpace (Sample n) := MeasurableSpace.pi
  let Wi : Sample n → ℝ := fun a => W (a i)
  let own := wholeOwnSigma n i
  have hWi : @Measurable (Sample n) ℝ full (inferInstance : MeasurableSpace ℝ) Wi := by
    dsimp [Wi]
    exact measurable_fst.comp (measurable_pi_apply i)
  have hm : own ≤ full := by
    change MeasurableSpace.comap (fun a : Sample n => W (a i)) inferInstance ≤ _
    exact Measurable.comap_le (f := fun a : Sample n => W (a i)) hWi
  letI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  have hXm : @Measurable (Sample n) ℝ full (inferInstance : MeasurableSpace ℝ)
      (fun a : Sample n => X (a i)) := by
    exact (measurable_of_countable bit).comp
      ((measurable_snd.fst).comp (measurable_pi_apply i))
  have hPm : @Measurable (Sample n) ℝ full (inferInstance : MeasurableSpace ℝ)
      (wholePrediction F i) := by
    exact (F.measurable_g (F.fold i)).comp
      (measurable_id.prodMk (measurable_fst.comp (measurable_pi_apply i)))
  apply (condIndepFun_iff_condExp_inter_preimage_eq_mul hXm hPm).2
  intro s t hs ht
  letI : MeasurableSpace (Sample n) := full
  let X_i : Sample n → ℝ := fun a => X (a i)
  let A : Sample n → ℝ := fun a =>
    Set.indicator (X_i ⁻¹' s) (fun _ => (1 : ℝ)) a
  let B : Sample n → ℝ := fun a =>
    Set.indicator ((wholePrediction F i) ⁻¹' t) (fun _ => (1 : ℝ)) a
  let J : Sample n → ℝ := fun a => A a * B a
  let Q : Sample n → ℝ := fun a => eventPropensity s (M.pi (Wi a))
  let T : Sample n → ℝ := fun a => Q a * condExp own μ B a
  have hAm : Measurable A := by
    exact measurable_const.indicator (hs.preimage hXm)
  have hBm : Measurable B := by
    exact measurable_const.indicator (ht.preimage hPm)
  have hJm : Measurable J := by
    dsimp [J]
    exact hAm.mul hBm
  have hQm : Measurable Q := by
    dsimp [Q]
    exact (measurable_const.sub (hM.measurable_pi.comp hWi)).mul measurable_const |>.add
      ((hM.measurable_pi.comp hWi).mul measurable_const)
  have hJint : Integrable J μ := by
    apply integrable_bdd01 μ J hJm
    intro a
    have hA' := indicator_bdd01 (X_i ⁻¹' s) a
    have hB' := indicator_bdd01 ((wholePrediction F i) ⁻¹' t) a
    dsimp [J, A, B]
    constructor
    · exact mul_nonneg hA'.1 hB'.1
    · calc
        _ ≤ 1 * B a := mul_le_mul_of_nonneg_right hA'.2 hB'.1
        _ ≤ 1 := by simpa using hB'.2
  have hpEval := measurePreserving_eval (fun _ : Fin n => M.law) i
  have hpiAE : ∀ᵐ a ∂μ, 0 ≤ M.pi (Wi a) ∧ M.pi (Wi a) ≤ 1 := by
    have hp := hpEval.quasiMeasurePreserving.ae hM.positivity
    filter_upwards [hp] with a ha
    constructor <;> dsimp [Wi] <;> linarith [hM.delta_pos]
  have hqAE : ∀ᵐ a ∂μ, 0 ≤ Q a ∧ Q a ≤ 1 := by
    filter_upwards [hpiAE] with a ha
    exact eventPropensity_bounds s ha
  have hQSM : StronglyMeasurable[own] Q := by
    have hqb : Measurable (fun w : ℝ => eventPropensity s (M.pi w)) := by
      exact (measurable_const.sub hM.measurable_pi).mul measurable_const |>.add
        (hM.measurable_pi.mul measurable_const)
    exact (hqb.comp (comap_measurable Wi)).stronglyMeasurable
  have hBint : Integrable B μ := by
    apply integrable_bdd01 μ B hBm
    intro a
    exact indicator_bdd01 ((wholePrediction F i) ⁻¹' t) a
  have hQBint : Integrable (fun a => Q a * B a) μ := by
    have hQBm : Measurable (fun a => Q a * B a) := hQm.mul hBm
    have hQBbounds : ∀ᵐ a ∂μ, 0 ≤ Q a * B a ∧ Q a * B a ≤ 1 := by
      filter_upwards [hqAE] with a hq
      have hB' := indicator_bdd01 ((wholePrediction F i) ⁻¹' t) a
      constructor
      · exact mul_nonneg hq.1 hB'.1
      · calc
          _ ≤ 1 * B a := mul_le_mul_of_nonneg_right hq.2 hB'.1
          _ ≤ 1 := by simpa using hB'.2
    apply memLp_one_iff_integrable.mp
    exact memLp_of_bounded (a := 0) (b := 1) hQBbounds hQBm.aestronglyMeasurable 1
  have hpull := condExp_mul_of_stronglyMeasurable_left hQSM hQBint hBint
  have hBCEsm : StronglyMeasurable[own] (condExp own μ B) := stronglyMeasurable_condExp
  have hTsm : StronglyMeasurable[own] T := by
    exact hQSM.mul hBCEsm
  have hTInt : Integrable T μ := by
    have hCEint : Integrable (condExp own μ (fun a => Q a * B a)) μ := integrable_condExp
    exact hCEint.congr hpull
  have hfactorSet : ∀ v : Set ℝ, MeasurableSet v →
      (∫ a in Wi ⁻¹' v, J a ∂μ) =
        ∫ a in Wi ⁻¹' v, Q a * B a ∂μ := by
    intro v hv
    let C : Sample n → ℝ := fun a =>
      Set.indicator (Wi ⁻¹' v) (fun _ => (1 : ℝ)) a
    have hCmeas : MeasurableSet (Wi ⁻¹' v) := hv.preimage hWi
    have hfac := joint_indicator_factor M hM F i s t v hs ht hv
    have hleft : (∫ a, C a * A a * B a ∂μ) =
        ∫ a in Wi ⁻¹' v, A a * B a ∂μ := by
      calc
        _ = ∫ a, (Wi ⁻¹' v).indicator (fun a => A a * B a) a ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with a
          by_cases ha : a ∈ Wi ⁻¹' v <;> simp [C, Set.indicator, ha] <;> ring
        _ = _ := integral_indicator (μ := μ) (f := fun a => A a * B a) hCmeas
    have hright : (∫ a, C a * Q a * B a ∂μ) =
        ∫ a in Wi ⁻¹' v, Q a * B a ∂μ := by
      calc
        _ = ∫ a, (Wi ⁻¹' v).indicator (fun a => Q a * B a) a ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with a
          by_cases ha : a ∈ Wi ⁻¹' v <;> simp [C, Set.indicator, ha] <;> ring
        _ = _ := integral_indicator (μ := μ) (f := fun a => Q a * B a) hCmeas
    have hfac' : (∫ a, C a * A a * B a ∂μ) =
        ∫ a, C a * Q a * B a ∂μ := by
      convert hfac using 1 <;> congr 1 <;> funext a <;>
        simp [C, A, B, Q, X_i, Wi, Set.mem_preimage]
    exact hleft.symm.trans (hfac'.trans hright)
  have hTset : ∀ v : Set ℝ, MeasurableSet v →
      (∫ a in Wi ⁻¹' v, T a ∂μ) = ∫ a in Wi ⁻¹' v, J a ∂μ := by
    intro v hv
    have hCmeas : MeasurableSet (Wi ⁻¹' v) := hv.preimage hWi
    have hCmeasOwn : MeasurableSet[own] (Wi ⁻¹' v) :=
      hv.preimage (comap_measurable Wi)
    calc
      _ = ∫ a in Wi ⁻¹' v, condExp own μ (fun a => Q a * B a) a ∂μ := by
        calc
          _ = ∫ a, (Wi ⁻¹' v).indicator T a ∂μ :=
            (integral_indicator (μ := μ) (f := T) hCmeas).symm
          _ = ∫ a, (Wi ⁻¹' v).indicator
              (fun a => condExp own μ (fun a => Q a * B a) a) a ∂μ := by
            apply integral_congr_ae
            filter_upwards [hpull] with a ha
            have hTa : T a = condExp own μ (fun a => Q a * B a) a := by
              dsimp [T]
              exact ha.symm
            by_cases hmem : a ∈ Wi ⁻¹' v <;>
              simp [Set.indicator, hmem, hTa]
          _ = _ := integral_indicator (μ := μ)
            (f := fun a => condExp own μ (fun a => Q a * B a) a) hCmeas
      _ = ∫ a in Wi ⁻¹' v, Q a * B a ∂μ :=
        setIntegral_condExp hm hQBint hCmeasOwn
      _ = _ := (hfactorSet v hv).symm
  have hTCE : T =ᵐ[μ] condExp own μ J := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hm hJint
      (fun _ _ _ => hTInt.integrableOn)
      (fun C hC _ => by
        obtain ⟨v, hv, rfl⟩ := hC
        exact hTset v hv)
      hTsm.aestronglyMeasurable
  have hJ_eq : J = fun a => Set.indicator
      (X_i ⁻¹' s ∩ (wholePrediction F i) ⁻¹' t) (fun _ => (1 : ℝ)) a := by
    funext a
    by_cases hx : X_i a ∈ s <;> by_cases hp : wholePrediction F i a ∈ t <;>
      simp [J, A, B, Set.indicator, hx, hp]
  have hJ_ae : J =ᵐ[μ] (fun a => Set.indicator
      (X_i ⁻¹' s ∩ (wholePrediction F i) ⁻¹' t) (fun _ => (1 : ℝ)) a) :=
    Filter.Eventually.of_forall (fun a => congrFun hJ_eq a)
  have hCEJ := condExp_congr_ae (m := own) hJ_ae
  have hXA := condExp_treatment_event M hM n i s hs
  filter_upwards [hTCE, hCEJ, hXA] with a hta hj hq
  calc
    condExp own μ (Set.indicator
        (X_i ⁻¹' s ∩ (wholePrediction F i) ⁻¹' t) (fun _ => (1 : ℝ))) a =
        condExp own μ J a := hj.symm
    _ = T a := hta.symm
    _ = Q a * condExp own μ B a := rfl
    _ = condExp own μ A a * condExp own μ B a := by
      rw [← hq]
