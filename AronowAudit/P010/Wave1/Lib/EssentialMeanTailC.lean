import AronowAudit.P010.P010_Population
import Mathlib.MeasureTheory.Function.EssSup

namespace AronowAudit.P010.Wave1

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

set_option maxHeartbeats 800000

/-- A nonnull event gives a probability law after normalization. -/
theorem tcElse_event_probability {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → B) (hf : Measurable f)
    (E : Set Ω) (_hE : MeasurableSet E) (hpos : 0 < μ E) :
    IsProbabilityMeasure (eventLaw μ f E) := by
  constructor
  simp only [eventLaw, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hf MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hpos.ne' (measure_ne_top μ E)

/-- The integral under the normalized image is exactly the event mean. -/
theorem tcElse_event_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (E : Set Ω) :
    (∫ x, x ∂eventLaw μ f E) = eventMean μ f E := by
  rw [eventLaw, integral_smul_measure]
  have he : (∫ x : ℝ, x ∂(μ.restrict E).map f) = ∫ x, f x ∂μ.restrict E :=
    integral_map hf.aemeasurable measurable_id'.aestronglyMeasurable
  rw [he]
  simp only [eventMean, ENNReal.toReal_inv, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- An integrable event outcome is integrable under its normalized image. -/
theorem tcElse_event_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (E : Set Ω) (hpos : 0 < μ E) (hi : Integrable f (μ.restrict E)) :
    Integrable (id : ℝ → ℝ) (eventLaw μ f E) := by
  unfold eventLaw
  apply (integrable_smul_measure (by simp [measure_ne_top])
    (by simpa using hpos.ne')).mpr
  exact (integrable_map_measure measurable_id.aestronglyMeasurable hf.aemeasurable).mpr hi

/-- Normalized outcome laws on nested events are absolutely continuous. -/
theorem tcElse_event_ac_subset {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (E P : Set Ω) (hsub : E ⊆ P) (_hP : 0 < μ P) :
    eventLaw μ f E ≪ eventLaw μ f P := by
  unfold eventLaw
  exact (((Measure.absolutelyContinuous_of_le
    (Measure.restrict_mono hsub le_rfl)).map hf).smul_left _).smul_right
      (by simpa using (measure_ne_top μ P))

/-- Strict a.e. lower bounds remain strict after taking an integrable mean. -/
theorem tcElse_integral_gt {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (f : Ω → ℝ)
    (hi : Integrable f G) (c : ℝ) (hc : ∀ᵐ x ∂G, c < f x) :
    c < ∫ x, f x ∂G := by
  have hp : 0 < ∫ x, f x - c ∂G := by
    apply (integral_pos_iff_support_of_nonneg_ae
      (hc.mono fun x hx => sub_nonneg.mpr hx.le) (hi.sub (integrable_const c))).mpr
    have he : Function.support (fun x => f x - c) =ᵐ[G] (univ : Set Ω) := by
      filter_upwards [hc] with x hx
      simp [ne_of_gt (sub_pos.mpr hx)]
    rw [measure_congr he, measure_univ]
    exact zero_lt_one
  simpa only [integral_sub hi (integrable_const c), integral_const,
    probReal_univ, one_smul, sub_pos] using hp

/-- Strict a.e. upper bounds remain strict after taking an integrable mean. -/
theorem tcElse_integral_lt {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (f : Ω → ℝ)
    (hi : Integrable f G) (c : ℝ) (hc : ∀ᵐ x ∂G, f x < c) :
    (∫ x, f x ∂G) < c := by
  have hp := tcElse_integral_gt G (fun x => -f x) hi.neg (-c)
    (hc.mono fun x hx => neg_lt_neg hx)
  simpa only [integral_neg, neg_lt_neg_iff] using hp

/-- Absolute continuity puts every integrable probability mean inside the
essential endpoints of the reference law, including infinite endpoints. -/
theorem tcElse_essential_mean_bounds (F G : Measure ℝ) [IsProbabilityMeasure G]
    (hGF : G ≪ F) (hi : Integrable (id : ℝ → ℝ) G) :
    essInf (fun x : ℝ => (x : EReal)) F ≤ ((∫ x, x ∂G : ℝ) : EReal) ∧
      ((∫ x, x ∂G : ℝ) : EReal) ≤ essSup (fun x : ℝ => (x : EReal)) F := by
  constructor
  · by_contra hn
    obtain ⟨c, hc, hc'⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
    have ha : ∀ᵐ x : ℝ ∂G, essInf (fun y : ℝ => (y : EReal)) F ≤ (x : EReal) :=
      hGF.ae_le (ae_essInf_le (μ := F) (f := fun x : ℝ => (x : EReal)))
    have hr : ∀ᵐ x ∂G, c < x := ha.mono fun x hx =>
      EReal.coe_lt_coe_iff.mp (hc'.trans_le hx)
    exact (not_lt_of_ge (tcElse_integral_gt G id hi c hr).le)
      (EReal.coe_lt_coe_iff.mp hc)
  · by_contra hn
    obtain ⟨c, hc, hc'⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
    have ha : ∀ᵐ x : ℝ ∂G, (x : EReal) ≤ essSup (fun y : ℝ => (y : EReal)) F :=
      hGF.ae_le (ae_le_essSup (μ := F) (f := fun x : ℝ => (x : EReal)))
    have hr : ∀ᵐ x ∂G, x < c := ha.mono fun x hx =>
      EReal.coe_lt_coe_iff.mp (hx.trans_lt hc)
    exact (not_lt_of_ge (tcElse_integral_lt G id hi c hr).le)
      (EReal.coe_lt_coe_iff.mp hc')

/-- An atomless reference law makes a finite essential lower endpoint
strict for every absolutely continuous integrable probability mean. -/
theorem tcElse_essential_mean_strict_lower (F G : Measure ℝ) [IsProbabilityMeasure G]
    (hGF : G ≪ F) (hF : Atomless F) (hi : Integrable (id : ℝ → ℝ) G)
    (l : ℝ) (hl : essInf (fun x : ℝ => (x : EReal)) F = (l : EReal)) :
    l < ∫ x, x ∂G := by
  apply tcElse_integral_gt G id hi l
  have ha : ∀ᵐ x : ℝ ∂G, essInf (fun y : ℝ => (y : EReal)) F ≤ (x : EReal) :=
      hGF.ae_le (ae_essInf_le (μ := F) (f := fun x : ℝ => (x : EReal)))
  have hn : ∀ᵐ x ∂G, x ∉ ({l} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp (hGF (hF l))
  filter_upwards [ha, hn] with x hx hn
  exact lt_of_le_of_ne (EReal.coe_le_coe_iff.mp (hl ▸ hx)) (Ne.symm hn)

/-- The corresponding strict upper-endpoint bound. -/
theorem tcElse_essential_mean_strict_upper (F G : Measure ℝ) [IsProbabilityMeasure G]
    (hGF : G ≪ F) (hF : Atomless F) (hi : Integrable (id : ℝ → ℝ) G)
    (u : ℝ) (hu : essSup (fun x : ℝ => (x : EReal)) F = (u : EReal)) :
    (∫ x, x ∂G) < u := by
  apply tcElse_integral_lt G id hi u
  have ha : ∀ᵐ x : ℝ ∂G, (x : EReal) ≤ essSup (fun y : ℝ => (y : EReal)) F :=
      hGF.ae_le (ae_le_essSup (μ := F) (f := fun x : ℝ => (x : EReal)))
  have hn : ∀ᵐ x ∂G, x ∉ ({u} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp (hGF (hF u))
  filter_upwards [ha, hn] with x hx hn
  exact lt_of_le_of_ne (EReal.coe_le_coe_iff.mp (hu ▸ hx)) hn

/-- Positive lower-tail mass is exactly the strict essential-infimum test. -/
theorem tcElse_lower_tail_pos_iff (F : Measure ℝ) (M : ℝ) :
    0 < F (Iio M) ↔ essInf (fun x : ℝ => (x : EReal)) F < (M : EReal) := by
  constructor
  · intro hp
    by_contra hn
    have ha : ∀ᵐ x : ℝ ∂F, essInf (fun y : ℝ => (y : EReal)) F ≤ (x : EReal) :=
      ae_essInf_le (μ := F) (f := fun x : ℝ => (x : EReal))
    have hz : F (Iio M) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      exact ha.mono fun x hx hxm =>
        not_lt_of_ge (EReal.coe_le_coe_iff.mp ((le_of_not_gt hn).trans hx)) hxm
    exact hp.ne' hz
  · intro hl
    by_contra hn
    have hz : F (Iio M) = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt hn)
    have ha : ∀ᵐ x : ℝ ∂F, (M : EReal) ≤ (x : EReal) := by
      have h := measure_eq_zero_iff_ae_notMem.mp hz
      exact h.mono fun x hx => EReal.coe_le_coe_iff.mpr (le_of_not_gt hx)
    exact not_le_of_gt hl (le_essInf_of_ae_le _ ha)

/-- Positive upper-tail mass is exactly the strict essential-supremum test. -/
theorem tcElse_upper_tail_pos_iff (F : Measure ℝ) (M : ℝ) :
    0 < F (Ioi M) ↔ (M : EReal) < essSup (fun x : ℝ => (x : EReal)) F := by
  constructor
  · intro hp
    by_contra hn
    have ha : ∀ᵐ x : ℝ ∂F, (x : EReal) ≤ essSup (fun y : ℝ => (y : EReal)) F :=
      ae_le_essSup (μ := F) (f := fun x : ℝ => (x : EReal))
    have hz : F (Ioi M) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      exact ha.mono fun x hx hxm =>
        not_lt_of_ge (EReal.coe_le_coe_iff.mp (hx.trans (le_of_not_gt hn))) hxm
    exact hp.ne' hz
  · intro hu
    by_contra hn
    have hz : F (Ioi M) = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt hn)
    have ha : ∀ᵐ x : ℝ ∂F, (x : EReal) ≤ (M : EReal) := by
      have h := measure_eq_zero_iff_ae_notMem.mp hz
      exact h.mono fun x hx => EReal.coe_le_coe_iff.mpr (le_of_not_gt hx)
    exact not_le_of_gt hu (essSup_le_of_ae_le _ ha)

/-- The infinite essential endpoints are characterized by positive mass in
every real lower and upper tail. -/
theorem tcElse_infinite_endpoints_iff (F : Measure ℝ) :
    (essInf (fun x : ℝ => (x : EReal)) F = ⊥ ∧
      essSup (fun x : ℝ => (x : EReal)) F = ⊤) ↔
      ((∀ M : ℝ, 0 < F (Iio M)) ∧ (∀ M : ℝ, 0 < F (Ioi M))) := by
  simp only [tcElse_lower_tail_pos_iff, tcElse_upper_tail_pos_iff,
    EReal.eq_bot_iff_forall_lt, EReal.eq_top_iff_forall_lt]

/-- Every positive-mass real event has a positive bounded slice. -/
theorem tcElse_positive_bounded_slice (F : Measure ℝ) (E : Set ℝ) (hpos : 0 < F E) :
    ∃ n : ℕ, 0 < F (E ∩ Icc (-(n : ℝ)) (n : ℝ)) := by
  have he : (⋃ n : ℕ, E ∩ Icc (-(n : ℝ)) (n : ℝ)) = E := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact hn.1
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      exact mem_iUnion.mpr ⟨n, hx, by
        exact ⟨by linarith [neg_le_abs x], (le_abs_self x).trans hn.le⟩⟩
  apply exists_measure_pos_of_not_measure_iUnion_null
  rw [he]
  exact hpos.ne'

/-- A bounded measurable restriction has an integrable identity coordinate. -/
theorem tcElse_bounded_slice_integrable (F : Measure ℝ) [IsFiniteMeasure F]
    (E : Set ℝ) (n : ℕ) :
    Integrable (id : ℝ → ℝ) (F.restrict (E ∩ Icc (-(n : ℝ)) (n : ℝ))) := by
  apply (integrable_const (n : ℝ)).mono' measurable_id.aestronglyMeasurable
  have ha := ae_restrict_mem₀ (μ := F)
    (show NullMeasurableSet (Icc (-(n : ℝ)) (n : ℝ)) F from
      measurableSet_Icc.nullMeasurableSet)
  have hm : F.restrict (E ∩ Icc (-(n : ℝ)) (n : ℝ)) ≤
      F.restrict (Icc (-(n : ℝ)) (n : ℝ)) := Measure.restrict_mono inter_subset_right le_rfl
  filter_upwards [ae_mono hm ha] with x hx
  exact (Real.norm_eq_abs x).symm ▸ abs_le.mpr hx

/-- Bounded slices approximate the essential infimum from above. This
also supplies arbitrarily negative finite means when the endpoint is bottom. -/
theorem tcElse_lower_bounded_tail (F : Measure ℝ) [IsFiniteMeasure F]
    (M : ℝ) (hM : essInf (fun x : ℝ => (x : EReal)) F < (M : EReal)) :
    ∃ n : ℕ, 0 < F (Iio M ∩ Icc (-(n : ℝ)) (n : ℝ)) ∧
      eventMean F id (Iio M ∩ Icc (-(n : ℝ)) (n : ℝ)) < M := by
  obtain ⟨n, hn⟩ := tcElse_positive_bounded_slice F (Iio M)
    ((tcElse_lower_tail_pos_iff F M).mpr hM)
  let E := Iio M ∩ Icc (-(n : ℝ)) (n : ℝ)
  have hE : MeasurableSet E := measurableSet_Iio.inter measurableSet_Icc
  letI tcElse_lower_tail_probability := tcElse_event_probability F id measurable_id E hE hn
  have hi := tcElse_event_integrable F id measurable_id E hn
    (tcElse_bounded_slice_integrable F (Iio M) n)
  have ha : ∀ᵐ x : ℝ ∂eventLaw F id E, x < M := by
    unfold eventLaw
    rw [Measure.map_id]
    have hm : ∀ᵐ x : ℝ ∂F.restrict E, x ∈ E := ae_restrict_mem hE
    exact Measure.smul_absolutelyContinuous.ae_le (hm.mono fun x hx => hx.1)
  refine ⟨n, hn, ?_⟩
  rw [← tcElse_event_integral F id measurable_id E]
  exact tcElse_integral_lt _ id hi M ha

/-- Bounded slices approximate the essential supremum from below,
including arbitrarily positive finite means at a top endpoint. -/
theorem tcElse_upper_bounded_tail (F : Measure ℝ) [IsFiniteMeasure F]
    (M : ℝ) (hM : (M : EReal) < essSup (fun x : ℝ => (x : EReal)) F) :
    ∃ n : ℕ, 0 < F (Ioi M ∩ Icc (-(n : ℝ)) (n : ℝ)) ∧
      M < eventMean F id (Ioi M ∩ Icc (-(n : ℝ)) (n : ℝ)) := by
  obtain ⟨n, hn⟩ := tcElse_positive_bounded_slice F (Ioi M)
    ((tcElse_upper_tail_pos_iff F M).mpr hM)
  let E := Ioi M ∩ Icc (-(n : ℝ)) (n : ℝ)
  have hE : MeasurableSet E := measurableSet_Ioi.inter measurableSet_Icc
  letI tcElse_upper_tail_probability := tcElse_event_probability F id measurable_id E hE hn
  have hi := tcElse_event_integrable F id measurable_id E hn
    (tcElse_bounded_slice_integrable F (Ioi M) n)
  have ha : ∀ᵐ x : ℝ ∂eventLaw F id E, M < x := by
    unfold eventLaw
    rw [Measure.map_id]
    have hm : ∀ᵐ x : ℝ ∂F.restrict E, x ∈ E := ae_restrict_mem hE
    exact Measure.smul_absolutelyContinuous.ae_le (hm.mono fun x hx => hx.1)
  refine ⟨n, hn, ?_⟩
  rw [← tcElse_event_integral F id measurable_id E]
  exact tcElse_integral_gt _ id hi M ha

end AronowAudit.P010.Wave1
