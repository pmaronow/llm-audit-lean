import AronowAudit.P001.Wave1.Lib.TailA.MedianProcess
import AronowAudit.P001.Wave1.Lib.TailA.MedianTransport

/-! Local regularity and weak-limit tools for the upper sample median. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace AronowAudit.P001.TailA

universe u
local instance instDecidableMedianWeak (p : Prop) : Decidable p := Classical.propDecidable p

/-- Only the law in a neighborhood of the unique median is required. -/
def LocalMedianData {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (m : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    (μ.map (X 0)).restrict (Metric.ball m δ) =
      (volume.restrict (Metric.ball m δ)).withDensity (fun x => ENNReal.ofReal (f x)) ∧
    (∀ x ∈ Metric.ball m δ, 0 ≤ f x) ∧
    AEMeasurable f (volume.restrict (Metric.ball m δ)) ∧
    ContinuousAt f m ∧ 0 < f m ∧
    cdf μ (X 0) m = 1/2 ∧
    (∀ x, x < m → cdf μ (X 0) x < 1/2) ∧
    (∀ x, m < x → 1/2 < cdf μ (X 0) x)

/-- Local absolute continuity excludes atoms throughout the density neighborhood. -/
theorem medianWeak_local_atomless {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (m : ℝ) (f : ℝ → ℝ)
    (hlocal : LocalMedianData μ X m f) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Metric.ball m δ, (μ.map (X 0)) {x} = 0 := by
  obtain ⟨δ, hδ, hf, _⟩ := hlocal
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have he := congrArg (fun ν : Measure ℝ => ν {x}) hf
  rw [Measure.restrict_apply (measurableSet_singleton x),
    Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hx)] at he
  rw [he]
  exact withDensity_absolutelyContinuous _ _ (by simp)

/-- The density is integrable on its neighborhood, a consequence of finite local mass. -/
theorem medianWeak_local_integrable {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (m δ : ℝ) (f : ℝ → ℝ)
    (hf : (μ.map (X 0)).restrict (Metric.ball m δ) =
      (volume.restrict (Metric.ball m δ)).withDensity (fun x => ENNReal.ofReal (f x)))
    (hfn : ∀ x ∈ Metric.ball m δ, 0 ≤ f x)
    (hfm : AEMeasurable f (volume.restrict (Metric.ball m δ))) :
    IntegrableOn f (Metric.ball m δ) := by
  apply (lintegral_ofReal_ne_top_iff_integrable hfm.aestronglyMeasurable ?_).mp
  · have he := congrArg (fun ν : Measure ℝ => ν Set.univ) hf
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at he
    rw [← he]
    exact measure_ne_top _ _
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hfn x hx

/-- Splitting off the lower tail identifies the CDF locally with an integrable density CDF. -/
theorem medianWeak_local_cdf_eq {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Measurable Y)
    (m δ : ℝ) (f : ℝ → ℝ)
    (hf : (μ.map Y).restrict (Metric.ball m δ) =
      (volume.restrict (Metric.ball m δ)).withDensity (fun x => ENNReal.ofReal (f x)))
    (hfi : IntegrableOn f (Metric.ball m δ))
    (hfn : ∀ x ∈ Metric.ball m δ, 0 ≤ f x)
    {t : ℝ} (ht : t ∈ Metric.ball m δ) :
    cdf μ Y t = (μ.map Y).real (Set.Iic (m - δ)) +
      ∫ x in Set.Iic t, (Metric.ball m δ).indicator f x := by
  let P := μ.map Y
  let g := (Metric.ball m δ).indicator f
  have hgi : Integrable g := (integrable_indicator_iff measurableSet_ball).mpr hfi
  have hgn : ∀ x, 0 ≤ g x := by
    intro x
    by_cases hx : x ∈ Metric.ball m δ <;> simp [g, hx, hfn]
  have hg : (volume.restrict (Metric.ball m δ)).withDensity
      (fun x => ENNReal.ofReal (f x)) = volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
    rw [← withDensity_indicator measurableSet_ball]
    congr 1
    funext x
    by_cases hx : x ∈ Metric.ball m δ <;> simp [g, Set.indicator, hx]
  have hs : Set.Iic t \ Metric.ball m δ = Set.Iic (m - δ) := by
    rw [Real.ball_eq_Ioo] at ht ⊢
    ext x
    simp only [Set.mem_sdiff, Set.mem_Iic, Set.mem_Ioo, not_and_or, not_lt]
    constructor
    · rintro ⟨hxt, hx | hx⟩
      · exact hx
      · linarith [ht.2]
    · intro hx
      exact ⟨by linarith [ht.1], Or.inl hx⟩
  have he := measureReal_sdiff_add_inter (μ := P) (s := Set.Iic t)
    (t := Metric.ball m δ) measurableSet_ball
  rw [hs] at he
  have hmass : P.real (Set.Iic t ∩ Metric.ball m δ) = ∫ x in Set.Iic t, g x := by
    change (P (Set.Iic t ∩ Metric.ball m δ)).toReal = _
    rw [← Measure.restrict_apply measurableSet_Iic, hf, hg,
      withDensity_apply _ measurableSet_Iic,
      ← ofReal_integral_eq_lintegral_ofReal hgi.integrableOn (ae_of_all _ hgn),
      ENNReal.toReal_ofReal (integral_nonneg hgn)]
  rw [hmass] at he
  change (μ (Y ⁻¹' Set.Iic t)).toReal = _
  rw [← Measure.map_apply hY measurableSet_Iic]
  exact he.symm

/-- The local density identity and continuity at the median give the exact CDF derivative. -/
theorem medianWeak_cdf_hasDerivAt {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : Measurable (X 0)) (m : ℝ) (f : ℝ → ℝ)
    (hlocal : LocalMedianData μ X m f) : HasDerivAt (cdf μ (X 0)) (f m) m := by
  obtain ⟨δ, hδ, hf, hfn, hfm, hc, _⟩ := hlocal
  let g := (Metric.ball m δ).indicator f
  have hgi : Integrable g := (integrable_indicator_iff measurableSet_ball).mpr
    (medianWeak_local_integrable μ X m δ f hf hfn hfm)
  have he : g =ᶠ[𝓝 m] f := by
    filter_upwards [Metric.ball_mem_nhds m hδ] with x hx
    exact Set.indicator_of_mem hx f
  have hgc : ContinuousAt g m := hc.congr_of_eventuallyEq he
  have hgm : g m = f m := he.eq_of_nhds
  have hd : HasDerivAt (fun t => ∫ x in Set.Iic t, g x) (f m) m := by
    have heq : (fun t => ∫ x in Set.Iic t, g x) =
        (fun t => (∫ x in Set.Iic m, g x) + ∫ x in m..t, g x) := by
      funext t
      have hh := intervalIntegral.integral_Iic_sub_Iic (a := m) (b := t)
        hgi.integrableOn hgi.integrableOn
      linarith
    rw [heq, ← hgm]
    exact (intervalIntegral.integral_hasDerivAt_right hgi.intervalIntegrable
      hgi.aestronglyMeasurable.stronglyMeasurableAtFilter hgc).const_add _
  apply (hd.const_add ((μ.map (X 0)).real (Set.Iic (m - δ)))).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds m hδ] with t ht
  exact medianWeak_local_cdf_eq μ (X 0) hX m δ f hf
    (medianWeak_local_integrable μ X m δ f hf hfn hfm) hfn ht

/-- A derivative controls fixed root-size local shifts, including the zero shift. -/
theorem medianWeak_scaled_derivative (F : ℝ → ℝ) (m d z : ℝ)
    (hd : HasDerivAt F d m) :
    Tendsto (fun n : ℕ => Real.sqrt n * (F (m + z / Real.sqrt n) - F m))
      atTop (𝓝 (d * z)) := by
  have hi : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hz : Tendsto (fun n : ℕ => m + z / Real.sqrt n) atTop (𝓝 m) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hi) :
        Tendsto (fun n : ℕ => m + z * (Real.sqrt n)⁻¹) atTop (𝓝 (m + z * 0)))
  have hlim := (hd.continuousAt_div.tendsto.comp hz).mul_const z
  convert hlim.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
    by_cases hz0 : z = 0
    · simp [hz0]
    · simp only [Function.comp_apply]
      rw [Function.update_of_ne (show m + z / Real.sqrt n ≠ m from by
        intro h; apply div_ne_zero hz0 hs; linarith)]
      simp only [add_sub_cancel_left]
      field_simp

/-- The upper-rank rounding error is between zero and one, for both parities. -/
theorem medianWeak_rank_error_bounds (n : ℕ) :
    0 ≤ ((n / 2 + 1 : ℕ) : ℝ) - (n : ℝ) / 2 ∧
    ((n / 2 + 1 : ℕ) : ℝ) - (n : ℝ) / 2 ≤ 1 := by
  have h1 : 2 * (n / 2) ≤ n := by omega
  have h2 : n ≤ 2 * (n / 2) + 1 := by omega
  have h1R : (2 : ℝ) * (n / 2 : ℕ) ≤ n := by exact_mod_cast h1
  have h2R : (n : ℝ) ≤ 2 * (n / 2 : ℕ) + 1 := by exact_mod_cast h2
  push_cast
  constructor <;> linarith

/-- The rank rounding vanishes on the root-size scale. -/
theorem medianWeak_rank_error_tendsto :
    Tendsto (fun n : ℕ => (((n / 2 + 1 : ℕ) : ℝ) - (n : ℝ) / 2) / Real.sqrt n)
      atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero
    (fun n => div_nonneg (medianWeak_rank_error_bounds n).1 (Real.sqrt_nonneg _))
    (fun n => div_le_div_of_nonneg_right (medianWeak_rank_error_bounds n).2 (Real.sqrt_nonneg _))
  simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- First-sample measurability is valid for the empty sample as well. -/
theorem medianWeak_sample_measurable {Ω : Type u} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (fun ω => sampleMedian (firstSample X n ω)) :=
  (upper_median_measurable n).comp (measurable_pi_iff.mpr fun i => hX i)

/-- Marginal median convergence from differentiability at the unique median.
Both sample-size parities and the empty initial sample are included. -/
theorem medianWeak_marginal_of_derivative {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : IID μ X) (m d : ℝ) (hdpos : 0 < d)
    (hmed : cdf μ (X 0) m = 1/2) (hd : HasDerivAt (cdf μ (X 0)) d m) :
    CD μ (fun n ω => Real.sqrt n * (sampleMedian (firstSample X n ω) - m))
      (gaussianReal 0 ⟨1/(4*d^2), by positivity⟩) := by
  intro z _
  let t := fun n : ℕ => m + z / Real.sqrt n
  let p := fun n : ℕ => cdf μ (X 0) (t n)
  let B := fun n (i : Fin n) (ω : Ω) => if X i ω ≤ t n then true else false
  let W := fun n (ω : Ω) =>
    ((∑ i : Fin n, if B n i ω then (1 : ℝ) else 0) - (n : ℝ) * p n) / Real.sqrt n
  let c : ℝ := -(1 / d)
  have ht : Tendsto t atTop (𝓝 m) := by
    have hi := tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa [t, div_eq_mul_inv] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hi) :
        Tendsto (fun n : ℕ => m + z * (Real.sqrt n)⁻¹) atTop (𝓝 (m + z * 0)))
  have hp : Tendsto p atTop (𝓝 (1/2 : ℝ)) := by
    simpa only [p, hmed, Function.comp_def] using hd.continuousAt.tendsto.comp ht
  have hB : ∀ n i, Measurable (B n i) := by
    intro n i
    exact Measurable.ite (measurableSet_le (hiid.1 i) measurable_const)
      measurable_const measurable_const
  have hi : ∀ n, iIndepFun (B n) μ := by
    intro n
    exact (hiid.2.1.precomp Fin.val_injective).comp
      (fun _ x => if x ≤ t n then true else false)
      (fun _ => Measurable.ite (measurableSet_le measurable_id measurable_const)
        measurable_const measurable_const)
  have hpB : ∀ n i, prob μ {ω | B n i ω = true} = p n := by
    intro n i
    have hmap := (hiid.2.2 i).map_eq
    have he := congrArg (fun ν : Measure ℝ => ν.real (Set.Iic (t n))) hmap
    simpa [Measure.real, Measure.map_apply (hiid.1 i) measurableSet_Iic,
      Measure.map_apply (hiid.1 0) measurableSet_Iic, Set.preimage, Set.mem_Iic, B, p, cdf, prob] using he
  have hw := bernoulliRows_tendstoInDistribution (fun _ => Ω) (fun _ => μ)
    (fun n => n) tendsto_id B p (1/2) hB hi hpB (by norm_num) hp
  have hy := hw.continuous_comp (g := fun x : ℝ => c * x) (by fun_prop)
  have hgauss : (gaussianReal 0
      ⟨(1/2 : ℝ) * (1 - 1/2), by norm_num⟩).map (fun x => c * x) =
      gaussianReal 0 ⟨1/(4*d^2), by positivity⟩ := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply Subtype.ext
      change c^2 * ((1/2 : ℝ) * (1-1/2)) = 1/(4*d^2)
      dsimp [c]
      field_simp
      <;> ring
  have hy' : TendstoInDistribution (fun n ω => c * W n ω) atTop (id : ℝ → ℝ)
      (fun _ => μ) (gaussianReal 0 ⟨1/(4*d^2), by positivity⟩) := by
    refine ⟨hy.forall_aemeasurable, aemeasurable_id, ?_⟩
    simpa only [Function.comp_def, id_eq, Measure.map_id, hgauss, W] using hy.tendsto
  let a := fun n : ℕ => c * ((((n/2+1 : ℕ) : ℝ) - (n : ℝ) * p n) / Real.sqrt n)
  have ha : Tendsto a atTop (𝓝 z) := by
    have hs := medianWeak_scaled_derivative (cdf μ (X 0)) m d z hd
    rw [hmed] at hs
    have hh := (medianWeak_rank_error_tendsto.sub hs).const_mul c
    have htarget : c * (0 - d * z) = z := by dsimp [c]; field_simp; ring
    rw [htarget] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hsR : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
    have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
    dsimp only [a, p, t]
    congr 1
    generalize cdf μ (X 0) (m + z / Real.sqrt n) = q
    field_simp
    rw [hsq]
    ring
  have hv : (⟨1/(4*d^2), by positivity⟩ : ℝ≥0) ≠ 0 := by
    exact ne_of_gt (show (0 : ℝ≥0) < ⟨1/(4*d^2), by positivity⟩ from by
      change 0 < 1/(4*d^2)
      positivity)
  letI instNullMedianWeakGaussian : NullSingletonClass
      (gaussianReal 0 ⟨1/(4*d^2), by positivity⟩) := nullSingletonClass_gaussianReal hv
  have hlim := (row_weak_moving_cdf hy'.forall_aemeasurable
    ((bernoulliRows_rowWeak_iff hy'.forall_aemeasurable).mpr hy') a z ha).1
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  congr 2
  ext ω
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hc : c < 0 := neg_neg_of_pos (one_div_pos.mpr hdpos)
  have hsum : (∑ i : Fin n, if B n i ω then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun i : Fin n => X i ω ≤ t n)).card : ℝ) := by
    rw [Finset.card_filter]
    simp [B]
  change c * W n ω ≤ a n ↔
    Real.sqrt n * (sampleMedian (firstSample X n ω) - m) ≤ z
  rw [show Real.sqrt n * (sampleMedian (firstSample X n ω) - m) ≤ z ↔
      sampleMedian (firstSample X n ω) ≤ t n by
    dsimp [t]; rw [← le_div_iff₀' hs]; constructor <;> intro h <;> linarith]
  rw [upper_median_count hn]
  dsimp only [W, a]
  rw [mul_le_mul_left_of_neg hc, div_le_div_iff_of_pos_right hs, hsum]
  rw [sub_le_sub_iff_right, Nat.cast_le]
  rfl

/-- The local-density assumptions suffice for the all-size marginal Gaussian limit. -/
theorem medianWeak_local_marginal {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : IID μ X) (m : ℝ) (f : ℝ → ℝ) (hlocal : LocalMedianData μ X m f) :
    CD μ (fun n ω => Real.sqrt n * (sampleMedian (firstSample X n ω) - m))
      (gaussianReal 0 ⟨1/(4*(f m)^2), by positivity⟩) := by
  have hderiv := medianWeak_cdf_hasDerivAt μ X (hiid.1 0) m f hlocal
  obtain ⟨δ, hδ, hf, hfn, hfm, hc, hp, hm, _⟩ := hlocal
  exact medianWeak_marginal_of_derivative μ X hiid m (f m) hp hm
    hderiv

/-- Independent observations cannot tie at any value in the atom-free neighborhood. -/
theorem medianWeak_no_local_ties {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : IID μ X) (m : ℝ) (f : ℝ → ℝ) (hlocal : LocalMedianData μ X m f) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ ω ∂μ,
      ∀ i j : ℕ, i ≠ j → X i ω ∈ Metric.ball m δ → X i ω ≠ X j ω := by
  obtain ⟨δ, hδ, ha⟩ := medianWeak_local_atomless μ X m f hlocal
  refine ⟨δ, hδ, ?_⟩
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i = j
  · exact ae_of_all _ fun _ h => (h hij).elim
  let P := μ.map (X 0)
  let A : Set (ℝ × ℝ) := {p | p.1 ∈ Metric.ball m δ ∧ p.1 = p.2}
  have hA : MeasurableSet A :=
    (measurableSet_ball.preimage measurable_fst).inter
      (measurableSet_eq_fun measurable_fst measurable_snd)
  have hz : P.prod P A = 0 := by
    apply Measure.measure_prod_null_of_ae_null hA
    exact ae_of_all _ fun x => by
      change P (Prod.mk x ⁻¹' A) = 0
      by_cases hx : x ∈ Metric.ball m δ
      · have he : Prod.mk x ⁻¹' A = {x} := by
          ext y
          change (x ∈ Metric.ball m δ ∧ x = y) ↔ y = x
          simp only [hx, true_and, eq_comm]
        rw [he]
        exact ha x hx
      · have he : Prod.mk x ⁻¹' A = ∅ := by
          ext y
          change (x ∈ Metric.ball m δ ∧ x = y) ↔ False
          simp only [hx, false_and]
        simp [he]
  have hmap : μ.map (fun ω => (X i ω, X j ω)) = P.prod P := by
    rw [(hiid.2.1.indepFun hij).map_prod_eq_prod_map_map (hiid.1 i).aemeasurable (hiid.1 j).aemeasurable,
      (hiid.2.2 i).map_eq, (hiid.2.2 j).map_eq]
  have hz' : μ {ω | X i ω ∈ Metric.ball m δ ∧ X i ω = X j ω} = 0 := by
    rw [← hmap, Measure.map_apply ((hiid.1 i).prodMk (hiid.1 j)) hA] at hz
    exact hz
  have hae : ∀ᵐ ω ∂μ, ¬(X i ω ∈ Metric.ball m δ ∧ X i ω = X j ω) := by
    rw [ae_iff]
    simpa only [not_not] using hz'
  filter_upwards [hae] with ω hω _ hx he
  exact hω ⟨hx, he⟩

/-- A sorted list has exactly `k+1` entries at or below its rank-`k` value when that
value occurs at most once. Duplicates at other values are allowed. -/
theorem medianWeak_sorted_unique_rank (l : List ℝ) (hl : l.Pairwise (· ≤ ·))
    (k : ℕ) (hk : k < l.length)
    (hone : (l.filter (fun a => a = l.getD k 0)).length ≤ 1) :
    (l.filter (fun a => a ≤ l.getD k 0)).length = k+1 := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    obtain ⟨ha, hs⟩ := List.pairwise_cons.mp hl
    cases k with
    | zero =>
      simp only [List.getD_cons_zero] at hone ⊢
      have he : l.filter (fun b => b = a) = [] := by
        apply List.length_eq_zero_iff.mp
        simpa using hone
      have hn : ∀ b ∈ l, ¬b ≤ a := by
        intro b hb hba
        have hbe : b = a := le_antisymm hba (ha b hb)
        have hm : b ∈ l.filter (fun b => b = a) := List.mem_filter.mpr ⟨hb, by simpa using hbe⟩
        simpa [he] using hm
      have hf : l.filter (fun b => b ≤ a) = [] := List.filter_eq_nil_iff.mpr (by simpa using hn)
      simp [hf]
    | succ k =>
      have hk' : k < l.length := by simpa using hk
      have hm : l.getD k 0 ∈ l := by
        rw [List.getD_eq_getElem l 0 hk']
        exact List.getElem_mem hk'
      have hal : a ≤ l.getD k 0 := ha _ hm
      have hone' : (l.filter (fun b => b = l.getD k 0)).length ≤ 1 := by
        simp only [List.getD_cons_succ, List.filter_cons] at hone
        split_ifs at hone <;> (try simp only [List.length_cons] at hone) <;> omega
      simpa only [List.getD_cons_succ, List.filter_cons, decide_eq_true_eq, hal,
        if_true, List.length_cons, Nat.add_assoc] using congrArg (· + 1) (ih hs k hk' hone')

/-- Sorting preserves the number of observations equal to a specified value. -/
theorem medianWeak_sorted_equal_card {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    (((List.ofFn x).mergeSort (fun a b => a ≤ b)).filter (fun a => a = t)).length =
      (Finset.univ.filter (fun i => x i = t)).card := by
  rw [((List.mergeSort_perm (List.ofFn x) (fun a b => a ≤ b)).filter
    (fun a => decide (a = t))).length_eq]
  simp only [Finset.card_filter]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    by_cases h : x 0 = t <;> simp [h, ih (fun i => x i.succ), Nat.add_comm]

/-- At a median that occurs only once, the empirical CDF equals the exact upper rank. -/
theorem medianWeak_cdf_at_unique_median {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hone : ∀ i j, x i = sampleMedian x → x j = sampleMedian x → i = j) :
    Literature.FiniteCDF x (sampleMedian x) = ((n/2+1 : ℕ) : ℝ) / n := by
  have hs : ((List.ofFn x).mergeSort (fun a b => a ≤ b)).Pairwise (· ≤ ·) :=
    List.pairwise_mergeSort' (· ≤ ·) _
  have hk : n/2 < ((List.ofFn x).mergeSort (fun a b => a ≤ b)).length := by
    simpa using Nat.div_lt_self hn (by norm_num : 1 < (2 : ℕ))
  have hone' : ((((List.ofFn x).mergeSort (fun a b => a ≤ b)).filter
      (fun a => a = sampleMedian x))).length ≤ 1 := by
    rw [medianWeak_sorted_equal_card]
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hone i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have he := medianWeak_sorted_unique_rank _ hs (n/2) hk hone'
  rw [medianCounts_sorted_filter_card] at he
  change (Finset.univ.filter (fun i => x i ≤ sampleMedian x)).card = n/2+1 at he
  unfold Literature.FiniteCDF
  have hc : (∑ i, if x i ≤ sampleMedian x then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun i => x i ≤ sampleMedian x)).card : ℝ) := by
    rw [Finset.card_filter]
    simp
  rw [hc, he]

/-- Positive derivative gives two-sided local CDF gaps with half the limiting slope. -/
theorem medianWeak_local_slopes {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : Measurable (X 0)) (m : ℝ) (f : ℝ → ℝ) (hlocal : LocalMedianData μ X m f) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Metric.ball m ρ,
      (x ≤ m → (f m/2)*(m-x) ≤ cdf μ (X 0) m - cdf μ (X 0) x) ∧
      (m ≤ x → (f m/2)*(x-m) ≤ cdf μ (X 0) x - cdf μ (X 0) m) := by
  have hd := medianWeak_cdf_hasDerivAt μ X hX m f hlocal
  have hp : 0 < f m := by obtain ⟨δ, hδ, hf, hn, hm, hc, hp, _⟩ := hlocal; exact hp
  let S := Function.update (fun x => (cdf μ (X 0) x - cdf μ (X 0) m)/(x-m)) m (f m)
  have hS : ContinuousAt S m := hd.continuousAt_div
  have hSm : S m = f m := Function.update_self _ _ _
  obtain ⟨ρ, hρ, hb⟩ := Metric.mem_nhds_iff.mp
    (hS.eventually (eventually_gt_nhds (show f m/2 < S m by rw [hSm]; linarith)))
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  by_cases he : x = m
  · subst x
    simp
  have hq : f m/2 ≤ (cdf μ (X 0) x - cdf μ (X 0) m)/(x-m) := by
    have hh0 : f m/2 < S x := hb hx
    have hh := hh0.le
    simpa only [S, Function.update_of_ne he] using hh
  constructor
  · intro hxm
    have hxneg : x-m < 0 := sub_neg.mpr (lt_of_le_of_ne hxm he)
    have hh := mul_le_mul_of_nonpos_right hq hxneg.le
    rw [div_mul_cancel₀ _ hxneg.ne] at hh
    linarith
  · intro hmx
    have hxpos : 0 < x-m := sub_pos.mpr (lt_of_le_of_ne hmx (Ne.symm he))
    have hh := mul_le_mul_of_nonneg_right hq hxpos.le
    rw [div_mul_cancel₀ _ hxpos.ne'] at hh
    exact hh

/-- The root-size median is tight under the local assumptions. -/
theorem medianWeak_root_tight {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : IID μ X) (m : ℝ) (f : ℝ → ℝ) (hlocal : LocalMedianData μ X m f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∀ᶠ (n : ℕ) in atTop,
      prob μ {ω | B < |Real.sqrt n * (sampleMedian (firstSample X n ω) - m)|} ≤ η := by
  have hp : 0 < f m := by obtain ⟨δ, hδ, hf, hn, hm, hc, hp, _⟩ := hlocal; exact hp
  have hv : (⟨1/(4*(f m)^2), by positivity⟩ : ℝ≥0) ≠ 0 :=
    ne_of_gt (show (0 : ℝ≥0) < ⟨1/(4*(f m)^2), by positivity⟩ from by
      change 0 < 1/(4*(f m)^2); positivity)
  letI instNullMedianTight : NullSingletonClass
      (gaussianReal 0 ⟨1/(4*(f m)^2), by positivity⟩) := nullSingletonClass_gaussianReal hv
  exact medianProcess_tight_of_cd μ _
    (fun n => ((medianWeak_sample_measurable X hiid.1 n).sub measurable_const).const_mul _)
    _ (medianWeak_local_marginal μ X hiid m f hlocal)

/-- Consistency follows from root-size tightness, without an integrability premise. -/
theorem medianWeak_consistency {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : IID μ X) (m : ℝ) (f : ℝ → ℝ) (hlocal : LocalMedianData μ X m f) :
    CP μ (fun n ω => sampleMedian (firstSample X n ω)) m := by
  have h0 := medianProcess_unscale_cp μ
    (fun n ω => Real.sqrt n * (sampleMedian (firstSample X n ω)-m))
    (medianWeak_root_tight μ X hiid m f hlocal)
  have h := probability_convergence_continuous_at μ _ 0 (fun z : ℝ => m+z) h0 (by fun_prop)
  simp only [add_zero] at h
  apply medianProcess_cp_congr μ h
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact ae_of_all _ fun ω => by
    have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
    field_simp
    <;> ring

/-- On the local no-tie event the empirical CDF at the median has only its
vanishing rank-rounding error on the root-size scale. -/
theorem medianWeak_rank_cp {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : IID μ X) (m : ℝ) (f : ℝ → ℝ) (hlocal : LocalMedianData μ X m f) :
    CP μ (fun n ω => Real.sqrt n *
      (Literature.FiniteCDF (firstSample X n ω) (sampleMedian (firstSample X n ω)) - 1/2)) 0 := by
  obtain ⟨δ, hδ, hties⟩ := medianWeak_no_local_ties μ X hiid m f hlocal
  have hc := medianWeak_consistency μ X hiid m f hlocal
  apply medianProcess_cp_on_good μ
    (medianProcess_cp_deterministic μ _ 0 medianWeak_rank_error_tendsto)
    (fun n => {ω | δ ≤ dist (sampleMedian (firstSample X n ω)) m}) (hc δ hδ)
  filter_upwards [eventually_gt_atTop 0] with n hn
  filter_upwards [hties] with ω ht hgood
  have hM : sampleMedian (firstSample X n ω) ∈ Metric.ball m δ := lt_of_not_ge hgood
  have huniq : ∀ i j : Fin n, firstSample X n ω i = sampleMedian (firstSample X n ω) →
      firstSample X n ω j = sampleMedian (firstSample X n ω) → i = j := by
    intro i j hi hj
    by_contra hij
    have hval : (i : ℕ) ≠ j := fun he => hij (Fin.ext he)
    apply ht i j hval
    · change X i ω = sampleMedian (firstSample X n ω) at hi
      rw [hi]
      exact hM
    · exact hi.trans hj.symm
  rw [medianWeak_cdf_at_unique_median hn _ huniq]
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
  field_simp <;> rw [hsq] <;> ring

/-- Deterministic root-size local empirical increments converge to the local CDF slope. -/
theorem medianWeak_local_increment {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : IID μ X) (m : ℝ) (f : ℝ → ℝ) (hlocal : LocalMedianData μ X m f) (t : ℝ) :
    CP μ (fun n ω => Real.sqrt n *
      (Literature.FiniteCDF (firstSample X n ω) (m+t/Real.sqrt n) -
        Literature.FiniteCDF (firstSample X n ω) m)) (f m*t) := by
  have hd := medianWeak_cdf_hasDerivAt μ X (hiid.1 0) m f hlocal
  have ht : Tendsto (fun n : ℕ => m+t/Real.sqrt n) atTop (𝓝 m) := by
    have hi := tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.add (tendsto_const_nhds.mul hi) :
      Tendsto (fun n : ℕ => m+t*(Real.sqrt n)⁻¹) atTop (𝓝 (m+t*0)))
  exact medianProcess_increment_cp μ X hiid m _ _
    (hd.continuousAt.tendsto.comp ht) (medianWeak_scaled_derivative _ m (f m) t hd)

/-- The empirical CDF evaluated at a root-size shift of the random sample median
has the required deterministic first-order expansion. -/
theorem medianWeak_random_expansion {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : IID μ X) (m : ℝ) (f : ℝ → ℝ) (hlocal : LocalMedianData μ X m f) (z : ℝ) :
    CP μ (fun n ω => Real.sqrt n *
      (Literature.FiniteCDF (firstSample X n ω)
        (sampleMedian (firstSample X n ω)+z/Real.sqrt n) - 1/2)) (f m*z) := by
  let T := fun n : ℕ => fun ω => Real.sqrt n * (sampleMedian (firstSample X n ω)-m)
  let U := fun n : ℕ => fun ω t => Real.sqrt n *
    (Literature.FiniteCDF (firstSample X n ω) (m+t/Real.sqrt n) -
      Literature.FiniteCDF (firstSample X n ω) m)
  have hp : 0 < f m := by obtain ⟨δ, hδ, hf, hn, hm, hc, hp, _⟩ := hlocal; exact hp
  have hmono : ∀ n ω, Monotone (U n ω) := by
    intro n ω a b hab
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply sub_le_sub_right
    unfold Literature.FiniteCDF
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    apply Finset.sum_le_sum
    intro i _
    have harg : m+a/Real.sqrt n ≤ m+b/Real.sqrt n :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hab (Real.sqrt_nonneg _))
    by_cases ha : firstSample X n ω i ≤ m+a/Real.sqrt n
    · simp only [if_pos ha, if_pos (ha.trans harg), le_refl]
    · split_ifs <;> norm_num
  have htight := medianWeak_root_tight μ X hiid m f hlocal
  have hpoint := fun t => medianWeak_local_increment μ X hiid m f hlocal t
  have h0 := medianProcess_random_threshold μ U (f m) hp.le hmono hpoint T htight
  have hz := medianProcess_random_threshold μ U (f m) hp.le hmono hpoint
    (fun n ω => T n ω+z) (medianProcess_tight_shift μ T htight z)
  have hn0 := probability_convergence_continuous_at μ _ 0 (fun x : ℝ => -x) h0 (by fun_prop)
  simp only [neg_zero] at hn0
  have hdiff := medianProcess_cp_add μ hz hn0
  simp only [add_zero] at hdiff
  have hshift := probability_convergence_continuous_at μ _ 0
    (fun x : ℝ => x+f m*z) hdiff (by fun_prop)
  simp only [zero_add] at hshift
  have h := medianProcess_cp_add μ hshift (medianWeak_rank_cp μ X hiid m f hlocal)
  simp only [add_zero] at h
  apply medianProcess_cp_congr μ h
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact ae_of_all _ fun ω => by
    have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
    have ha : m+(T n ω+z)/Real.sqrt n = sampleMedian (firstSample X n ω)+z/Real.sqrt n := by
      dsimp [T]; field_simp; ring
    have hb : m+T n ω/Real.sqrt n = sampleMedian (firstSample X n ω) := by
      dsimp [T]; field_simp; ring
    dsimp only [U]
    rw [ha, hb]
    ring

/-- The conditional Bernoulli parameter is the finite empirical CDF, even at size zero. -/
theorem medianWeak_parameter_eq {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    (empiricalThresholdProbability x t : ℝ) = Literature.FiniteCDF x t := by
  rw [empirical_threshold_probability_eq, Finset.card_filter]
  simp only [Literature.FiniteCDF, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Moving empirical Bernoulli parameters are measurable functions of the data. -/
theorem medianWeak_parameter_measurable {Ω : Type u} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (n : ℕ)
    (t : Ω → ℝ) (ht : Measurable t) :
    Measurable (fun ω => empiricalThresholdProbability (firstSample X n ω) (t ω)) := by
  have hm : Measurable (fun ω => (empiricalThresholdProbability (firstSample X n ω) (t ω) : ℝ)) := by
    simp only [medianWeak_parameter_eq, Literature.FiniteCDF]
    simpa only [firstSample] using
      (((Finset.univ : Finset (Fin n)).measurable_sum fun i _ => Measurable.ite
        (measurableSet_le (hX i) ht) measurable_const measurable_const).div_const (n : ℝ) :
        Measurable (fun ω => (∑ i : Fin n, if X i ω ≤ t ω then (1 : ℝ) else 0)/(n : ℝ)))
  exact hm.subtype_mk

/-- The strict standardized binomial CDF is the complement of the upper-rank event. -/
theorem medianWeak_binomial_upper (n : ℕ) (hn : 0 < n) (p : unitInterval) :
    prob (binomial n p) {k | n/2+1 ≤ k} =
      1-binomialCountStrictCDF n p ((((n/2+1 : ℕ) : ℝ)-(n : ℝ)*(p : ℝ))/Real.sqrt n) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have he : {k : ℕ | ((k : ℝ)-(n : ℝ)*(p : ℝ))/Real.sqrt n <
      (((n/2+1 : ℕ) : ℝ)-(n : ℝ)*(p : ℝ))/Real.sqrt n} = {k : ℕ | k < n/2+1} := by
    ext k
    simp only [Set.mem_setOf_eq]
    rw [div_lt_div_iff_of_pos_right hs, sub_lt_sub_iff_right, Nat.cast_lt]
  unfold binomialCountStrictCDF
  rw [he]
  have hh := measureReal_compl (μ := binomial n p) (s := {k : ℕ | k < n/2+1})
    MeasurableSet.of_discrete
  simpa only [prob, Measure.real, Set.compl_setOf, not_lt, measure_univ, ENNReal.toReal_one] using hh

/-- The exact conditional centered-median CDF uses the original data's moving
threshold parameter and the upper-rank binomial cutoff. -/
theorem medianWeak_bootstrap_cdf_formula {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (z : ℝ) :
    (CenteredBootstrapLaw sampleMedian x).real (Set.Iic z) =
      1-binomialCountStrictCDF n
        (empiricalThresholdProbability x (sampleMedian x+z/Real.sqrt n))
        ((((n/2+1 : ℕ) : ℝ)-(n : ℝ)*
          (empiricalThresholdProbability x (sampleMedian x+z/Real.sqrt n) : ℝ))/Real.sqrt n) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have he : {a : Fin n → Fin n | Real.sqrt n * (sampleMedian (resample x a)-sampleMedian x) ≤ z} =
      {a | sampleMedian (resample x a) ≤ sampleMedian x+z/Real.sqrt n} := by
    ext a
    simp only [Set.mem_setOf_eq]
    rw [← le_div_iff₀' hs]
    constructor <;> intro h <;> linarith
  change (((UniformResampling n).map _ ) (Set.Iic z)).toReal = _
  rw [Measure.map_apply Measurable.of_discrete measurableSet_Iic]
  change prob (UniformResampling n)
    {a | Real.sqrt n * (sampleMedian (resample x a)-sampleMedian x) ≤ z} = _
  rw [he, upper_median_bootstrap_probability hn, medianWeak_binomial_upper n hn]

/-- Gaussian rescaling identifies the complement of the count limit with the
median Gaussian CDF. -/
theorem medianWeak_gaussian_cdf (d : ℝ) (hd : 0 < d) (z : ℝ) :
    1-prob (gaussianReal 0 (1/4)) (Set.Iic (-d*z)) =
      prob (gaussianReal 0 ⟨1/(4*d^2), by positivity⟩) (Set.Iic z) := by
  let c : ℝ := -(1/d)
  let G := gaussianReal 0 (1/4)
  letI instNullMedianCountGaussian : NullSingletonClass G :=
    nullSingletonClass_gaussianReal (by norm_num : (1/4 : ℝ≥0) ≠ 0)
  have hmap : G.map (fun w => c*w) = gaussianReal 0 ⟨1/(4*d^2), by positivity⟩ := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply Subtype.ext
      change c^2 * (1/4 : ℝ) = 1/(4*d^2)
      dsimp [c]
      field_simp
      <;> ring
  have hc : c < 0 := neg_neg_of_pos (one_div_pos.mpr hd)
  have hcz : c*(-d*z) = z := by dsimp [c]; field_simp <;> ring
  have hpre : (fun w => c*w) ⁻¹' Set.Iic z = (Set.Iio (-d*z))ᶜ := by
    ext w
    change c*w ≤ z ↔ ¬w < -d*z
    rw [not_lt]
    calc
      c*w ≤ z ↔ c*w ≤ c*(-d*z) := by rw [hcz]
      _ ↔ -d*z ≤ w := mul_le_mul_left_of_neg hc
  rw [← hmap]
  change 1-G.real (Set.Iic (-d*z)) = (G.map (fun w => c*w)).real (Set.Iic z)
  rw [map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre,
    measureReal_compl measurableSet_Iio,
    measureReal_congr (μ := G) Iio_ae_eq_Iic]
  simp

/-- Conditional centered-median CDF convergence in probability, with no moment. -/
theorem medianWeak_conditional_cdf {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : IID μ X) (m : ℝ) (f : ℝ → ℝ) (hlocal : LocalMedianData μ X m f) (z : ℝ) :
    CP μ (fun n ω => (CenteredBootstrapLaw sampleMedian (firstSample X n ω)).real (Set.Iic z))
      ((gaussianReal 0 ⟨1/(4*(f m)^2), by positivity⟩).real (Set.Iic z)) := by
  let p := fun n : ℕ => fun ω => empiricalThresholdProbability (firstSample X n ω)
    (sampleMedian (firstSample X n ω)+z/Real.sqrt n)
  let A := fun n : ℕ => fun ω => Real.sqrt n * ((p n ω : ℝ)-1/2)
  let t := fun n : ℕ => fun ω =>
    ((((n/2+1 : ℕ) : ℝ)-(n : ℝ)*(p n ω : ℝ))/Real.sqrt n)
  have hpmeas : ∀ n, Measurable (p n) := by
    intro n
    exact medianWeak_parameter_measurable X hiid.1 n _
      ((medianWeak_sample_measurable X hiid.1 n).add measurable_const)
  have hA : CP μ A (f m*z) := by
    simpa only [A, p, medianWeak_parameter_eq] using medianWeak_random_expansion μ X hiid m f hlocal z
  have hu := medianProcess_unscale_cp μ A (medianProcess_tight_of_cp μ hA)
  have hp : CP μ (fun n ω => (p n ω : ℝ)) (1/2) := by
    have hh := probability_convergence_continuous_at μ _ 0 (fun x : ℝ => 1/2+x) hu (by fun_prop)
    simp only [add_zero] at hh
    apply medianProcess_cp_congr μ hh
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact ae_of_all _ fun ω => by
      have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
      dsimp only [A]
      field_simp
      <;> ring
  have ht : CP μ t (-(f m*z)) := by
    have hnA := probability_convergence_continuous_at μ A (f m*z) (fun x : ℝ => -x) hA (by fun_prop)
    have hh := medianProcess_cp_add μ (medianProcess_cp_deterministic μ _ 0 medianWeak_rank_error_tendsto) hnA
    simp only [zero_add] at hh
    apply medianProcess_cp_congr μ hh
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact ae_of_all _ fun ω => by
      have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
      have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
      dsimp only [t, A]
      generalize (p n ω : ℝ) = q
      field_simp
      rw [hsq]
      ring
  have htmeas : ∀ n, Measurable (t n) := by
    intro n
    exact (measurable_const.sub ((hpmeas n).subtype_coe.const_mul _)).div_const _
  have hbin := (random_binomial_moving_cdf μ (fun n => n) tendsto_id p (1/2)
    (by norm_num) hpmeas hp t (-(f m*z)) htmeas ht).2
  have hvar : (⟨(1/2 : ℝ)*(1-1/2), by norm_num⟩ : ℝ≥0) = 1/4 := by
    apply Subtype.ext
    change (1/2 : ℝ)*(1-1/2) = (1 : ℝ)/4
    norm_num
  rw [hvar] at hbin
  have hcomp := probability_convergence_continuous_at μ _ _ (fun x : ℝ => 1-x) hbin (by fun_prop)
  have hpos : 0 < f m := by obtain ⟨δ, hδ, hf, hn, hm, hc, hp, _⟩ := hlocal; exact hp
  rw [show -(f m*z) = -(f m)*z from by ring, medianWeak_gaussian_cdf (f m) hpos z] at hcomp
  apply medianProcess_cp_congr μ hcomp
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact ae_of_all _ fun ω => medianWeak_bootstrap_cdf_formula hn (firstSample X n ω) z

/-- All-size, moment-free marginal and conditional weak limits for the upper median. -/
theorem local_median_weak {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : IID μ X) (m : ℝ) (f : ℝ → ℝ) (hlocal : LocalMedianData μ X m f) :
    CD μ (fun n ω => Real.sqrt n * (sampleMedian (firstSample X n ω)-m))
      (gaussianReal 0 ⟨1/(4*(f m)^2), by positivity⟩) ∧
    BootstrapWeakCP μ X (fun n => n) (fun {n} => @sampleMedian n)
      (gaussianReal 0 ⟨1/(4*(f m)^2), by positivity⟩) := by
  refine ⟨medianWeak_local_marginal μ X hiid m f hlocal, ?_⟩
  apply medianTransport_bootstrap_of_cdf μ X (fun {n} => @sampleMedian n)
  exact medianWeak_conditional_cdf μ X hiid m f hlocal

end AronowAudit.P001.TailA
