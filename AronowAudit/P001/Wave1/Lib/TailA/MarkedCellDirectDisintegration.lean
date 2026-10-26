import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectPairSampling
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Real-score disintegration of the exact recipient sampling identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectDisintegration (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- The score subprobability law for either response type, including the sign
marginal, has the exact affine density on the actual score support. -/
theorem marked_type_score_marginal (r : Bool) :
    (matchingUnitLaw.restrict {u : MatchUnit | u.2.1 = r}).map Prod.fst =
      (volume.restrict (Set.Icc (1/4 : ℝ) (3/4))).withDensity
        (fun x => ENNReal.ofReal (markedTypeDensity r x)) := by
  have hs : MeasurableSet {u : MatchUnit | u.2.1 = r} :=
    measurableSet_eq_fun measurable_snd.fst measurable_const
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_fst,← lintegral_indicator hs]
  rw [matching_lintegral (fun u => ({u : MatchUnit | u.2.1 = r}).indicator
    (fun u => f u.1) u) ((hf.comp measurable_fst).indicator hs)]
  rw [lintegral_withDensity_eq_lintegral_mul _
    (marked_type_density_continuous r).measurable.ennreal_ofReal hf]
  apply lintegral_congr
  intro x
  cases r <;> simp [Set.indicator,markedTypeDensity,ENNReal.ofReal_mul] <;> ring

/-- An exact real integral identity, valid for every measurable score test. -/
theorem marked_type_score_integral (r : Bool) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ u : MatchUnit, (if u.2.1 = r then f u.1 else 0) ∂matchingUnitLaw) =
      ∫ x in Set.Icc (1/4 : ℝ) (3/4), markedTypeDensity r x*f x := by
  have hs : MeasurableSet {u : MatchUnit | u.2.1 = r} :=
    measurableSet_eq_fun measurable_snd.fst measurable_const
  have he : (fun u : MatchUnit => if u.2.1 = r then f u.1 else 0) =
      ({u : MatchUnit | u.2.1 = r}).indicator (fun u => f u.1) := by
    funext u
    by_cases h : u.2.1 = r <;> simp [h,Set.indicator]
  rw [he]
  rw [integral_indicator hs,← integral_map measurable_fst.aemeasurable
    hf.aestronglyMeasurable,marked_type_score_marginal r]
  rw [integral_withDensity_eq_integral_toReal_smul
    (marked_type_density_continuous r).measurable.ennreal_ofReal
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hn : 0 ≤ markedTypeDensity r x := by
    cases r <;> simp only [markedTypeDensity,Bool.false_eq_true,ite_false,ite_true]
      <;> linarith [hx.1,hx.2]
  simp only [ENNReal.toReal_ofReal hn,smul_eq_mul]

/-- Measurability of the unscaled one-query expectation. -/
theorem marked_unscaled_count_kernel_measurable (n : ℕ) (p : ℝ) (K : ℕ → ℝ) :
    Measurable (fun x : ℝ => mean (MatchProduct n) (fun z =>
      K (markedWindowCount (markedCloserDonors p x) z))) := by
  exact (((measurable_of_countable K).comp
    (marked_query_count_measurable n p Prod.fst Prod.snd measurable_fst measurable_snd )).stronglyMeasurable.integral_prod_right').measurable

/-- The individual and union counts are averaged in the same original sample. -/
theorem marked_unscaled_pair_kernel_measurable (n : ℕ) (p : ℝ)
    (K : ℕ → ℕ → ℕ → ℝ) :
    Measurable (fun q : ℝ × ℝ => mean (MatchProduct n) (fun z =>
      K (markedWindowCount (markedCloserDonors p q.1) z)
        (markedWindowCount (markedCloserDonors p q.2) z)
        (markedWindowCount (markedCloserDonors p q.1 ∪ markedCloserDonors p q.2) z))) := by
  have h1 := marked_query_count_measurable n p
    (fun y : (ℝ × ℝ) × (Fin n → MatchUnit) => y.1.1) Prod.snd
    measurable_fst.fst measurable_snd
  have h2 := marked_query_count_measurable n p
    (fun y : (ℝ × ℝ) × (Fin n → MatchUnit) => y.1.2) Prod.snd
    measurable_fst.snd measurable_snd
  have h3 := marked_query_union_count_measurable n p
    (fun y : (ℝ × ℝ) × (Fin n → MatchUnit) => y.1.1)
    (fun y => y.1.2) Prod.snd measurable_fst.fst measurable_fst.snd measurable_snd
  have hK : Measurable (fun c : ℕ × ℕ × ℕ => K c.1 c.2.1 c.2.2) := measurable_of_countable _
  exact ((hK.comp (h1.prodMk (h2.prodMk h3))).stronglyMeasurable.integral_prod_right').measurable

/-- One fixed recipient leaves exactly `n` iid observations, and has density
`2(1-x)` rather than the donor density `2x`. -/
theorem marked_recipient_score_disintegration (n : ℕ) (p : ℝ) (K : ℕ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hK : ∀ c, |K c| ≤ C) :
    mean (MatchProduct (n+1)) (fun z => markedRecipientCountTest p K z 0) =
      ∫ x in Set.Icc (1/4 : ℝ) (3/4), 2*(1-x)*
        mean (MatchProduct n) (fun z => K (markedWindowCount (markedCloserDonors p x) z)) := by
  rw [marked_recipient_count_test_disintegration n p K hC hK]
  have he (u : MatchUnit) :
      (∫ z, (if u.2.1 = false then K (markedWindowCount (markedCloserDonors p u.1) z)
        else 0) ∂MatchProduct n) =
      if u.2.1 = false then mean (MatchProduct n)
        (fun z => K (markedWindowCount (markedCloserDonors p u.1) z)) else 0 := by
    by_cases h : u.2.1 = false <;> simp [h,mean]
  simp_rw [he]
  exact marked_type_score_integral false _ (marked_unscaled_count_kernel_measurable n p K)

/-- Two fixed recipients have their two actual affine densities and leave
exactly `n` independent original observations in the shared donor environment. -/
theorem marked_recipient_pair_score_disintegration (n : ℕ) (p : ℝ)
    (K : ℕ → ℕ → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) (hK : ∀ a b c, |K a b c| ≤ C) :
    mean (MatchProduct (n+2)) (fun z => markedRecipientPairCountTest p K z 0 1) =
      ∫ x in Set.Icc (1/4 : ℝ) (3/4), 2*(1-x)*
        (∫ y in Set.Icc (1/4 : ℝ) (3/4), 2*(1-y)*mean (MatchProduct n) (fun z =>
          K (markedWindowCount (markedCloserDonors p x) z)
            (markedWindowCount (markedCloserDonors p y) z)
            (markedWindowCount (markedCloserDonors p x ∪ markedCloserDonors p y) z))) := by
  let H : ℝ × ℝ → ℝ := fun q => mean (MatchProduct n) (fun z =>
    K (markedWindowCount (markedCloserDonors p q.1) z)
      (markedWindowCount (markedCloserDonors p q.2) z)
      (markedWindowCount (markedCloserDonors p q.1 ∪ markedCloserDonors p q.2) z))
  have hH : Measurable H := marked_unscaled_pair_kernel_measurable n p K
  have he (u v : MatchUnit) :
      (∫ z, (if u.2.1 = false ∧ v.2.1 = false then
        K (markedWindowCount (markedCloserDonors p u.1) z)
          (markedWindowCount (markedCloserDonors p v.1) z)
          (markedWindowCount (markedCloserDonors p u.1 ∪ markedCloserDonors p v.1) z)
        else 0) ∂MatchProduct n) =
      if u.2.1 = false ∧ v.2.1 = false then H (u.1,v.1) else 0 := by
    by_cases h : u.2.1 = false ∧ v.2.1 = false <;> simp [h,H,mean]
  have hv (u : MatchUnit) :
      (∫ v, (if u.2.1 = false ∧ v.2.1 = false then H (u.1,v.1) else 0) ∂matchingUnitLaw) =
      if u.2.1 = false then
        ∫ y in Set.Icc (1/4 : ℝ) (3/4), 2*(1-y)*H (u.1,y) else 0 := by
    by_cases hu : u.2.1 = false
    · simp only [hu,true_and,ite_true]
      exact marked_type_score_integral false _ (hH.comp (measurable_const.prodMk measurable_id))
    · simp [hu]
  rw [marked_recipient_pair_test_disintegration n p K hC hK]
  simp_rw [he,hv]
  have hG : Measurable (fun x : ℝ => ∫ y in Set.Icc (1/4 : ℝ) (3/4), 2*(1-y)*H (x,y)) :=
    (((((marked_type_density_continuous false).measurable.comp measurable_snd).mul hH).stronglyMeasurable.integral_prod_right').measurable)
  simpa only [H,markedTypeDensity,Bool.false_eq_true,ite_false] using
    marked_type_score_integral false _ hG

/-- Affine change of variables with its exact finite Jacobian. -/
theorem marked_recipient_affine_integral (m : ℕ) (p : ℝ) (f : ℝ → ℝ) :
    (∫ t : ℝ, markedScaledRecipientDensity m p t*f (p+t/(m : ℝ))) =
      (m : ℝ)*(∫ x in Set.Icc (1/4 : ℝ) (3/4), 2*(1-x)*f x) := by
  let g : ℝ → ℝ := (Set.Icc (1/4 : ℝ) (3/4)).indicator (fun x => 2*(1-x)*f x)
  have he (t : ℝ) : markedScaledRecipientDensity m p t*f (p+t/(m : ℝ)) =
      g (p+t/(m : ℝ)) := by
    simp only [markedScaledRecipientDensity,g,Set.indicator]
    split_ifs <;> simp
  simp_rw [he]
  rw [Measure.integral_comp_div (fun x => g (p+x)) (m : ℝ),
    integral_add_left_eq_self g p,abs_of_nonneg (Nat.cast_nonneg _),smul_eq_mul]
  simp only [g,integral_indicator measurableSet_Icc]

/-- Two affine changes of variables retain the exact squared Jacobian. -/
theorem marked_recipient_pair_affine_integral (m : ℕ) (p : ℝ) (f : ℝ → ℝ → ℝ) :
    (∫ t : ℝ, markedScaledRecipientDensity m p t *
      (∫ u : ℝ, markedScaledRecipientDensity m p u*f (p+t/(m : ℝ)) (p+u/(m : ℝ)))) =
      (m : ℝ)^2*(∫ x in Set.Icc (1/4 : ℝ) (3/4), 2*(1-x)*
        (∫ y in Set.Icc (1/4 : ℝ) (3/4), 2*(1-y)*f x y)) := by
  simp_rw [marked_recipient_affine_integral m p]
  have he (t : ℝ) : markedScaledRecipientDensity m p t *
      ((m : ℝ)*(∫ y in Set.Icc (1/4 : ℝ) (3/4), 2*(1-y)*f (p+t/(m : ℝ)) y)) =
      (m : ℝ)*(markedScaledRecipientDensity m p t *
        (∫ y in Set.Icc (1/4 : ℝ) (3/4), 2*(1-y)*f (p+t/(m : ℝ)) y)) := by ring
  simp_rw [he]
  rw [integral_const_mul,marked_recipient_affine_integral m p
    (fun x => ∫ y in Set.Icc (1/4 : ℝ) (3/4), 2*(1-y)*f x y)]
  ring

/-- Full one-recipient sampling identity in the scaled position coordinates.
When its kernel comes from a pinned bootstrap, its bootstrap size is `m+2`. -/
theorem marked_recipient_scaled_sum_integral (m : ℕ) (hm : 0 < m) (p : ℝ) (K : ℕ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hK : ∀ c, |K c| ≤ C) :
    mean (MatchProduct (m+1)) (fun z => ∑ i, markedRecipientCountTest p K z i) =
      ((m+1 : ℕ) : ℝ)/(m : ℝ) * (∫ t : ℝ, markedScaledRecipientDensity m p t *
        mean (MatchProduct m) (fun z =>
          K (markedWindowCount (markedCloserDonors p (p+t/(m : ℝ))) z))) := by
  rw [marked_recipient_count_sum_integral m p K hC hK,
    marked_recipient_score_disintegration m p K hC hK,
    marked_recipient_affine_integral m p (fun x => mean (MatchProduct m)
      (fun z => K (markedWindowCount (markedCloserDonors p x) z)))]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp

/-- Full distinct-recipient identity with the exact two-position sampling
factor. The pinned-bootstrap kernels here have bootstrap size `m+3`. -/
theorem marked_recipient_pair_scaled_sum_integral (m : ℕ) (hm : 0 < m) (p : ℝ)
    (K : ℕ → ℕ → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) (hK : ∀ a b c, |K a b c| ≤ C) :
    mean (MatchProduct (m+2)) (fun z => ∑ i, ∑ j,
      if i = j then 0 else markedRecipientPairCountTest p K z i j) =
      (((m+2 : ℕ) : ℝ)*(m+1 : ℕ)/(m : ℝ)^2) *
        (∫ t : ℝ, markedScaledRecipientDensity m p t *
          (∫ u : ℝ, markedScaledRecipientDensity m p u * mean (MatchProduct m) (fun z =>
            K (markedWindowCount (markedCloserDonors p (p+t/(m : ℝ))) z)
              (markedWindowCount (markedCloserDonors p (p+u/(m : ℝ))) z)
              (markedWindowCount (markedCloserDonors p (p+t/(m : ℝ)) ∪
                markedCloserDonors p (p+u/(m : ℝ))) z)))) := by
  rw [marked_recipient_pair_sum_integral m p K hC hK,
    marked_recipient_pair_score_disintegration m p K hC hK,
    marked_recipient_pair_affine_integral m p (fun x y => mean (MatchProduct m) (fun z =>
      K (markedWindowCount (markedCloserDonors p x) z)
        (markedWindowCount (markedCloserDonors p y) z)
        (markedWindowCount (markedCloserDonors p x ∪ markedCloserDonors p y) z)))]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp

/-- Both finite sampling factors tend to one. -/
theorem marked_recipient_sampling_factor_limits :
    Tendsto (fun m : ℕ => ((m+1 : ℕ) : ℝ)/(m : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun m : ℕ => ((m+2 : ℕ) : ℝ)*(m+1 : ℕ)/(m : ℝ)^2) atTop (𝓝 1) := by
  have hi : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun m : ℕ => 1+(m : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hi
  have h2 : Tendsto (fun m : ℕ => 1+2*(m : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [mul_zero,add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add (hi.const_mul 2)
  constructor
  · apply h1.congr'
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  · have hh := h2.mul h1
    simp only [mul_one] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    <;> ring

end AronowAudit.P001.TailA
