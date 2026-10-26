import AronowAudit.P001.Wave1.Lib.TailA.MedianCounts
import AronowAudit.P037.P037_VaryingLindeberg
import AronowAudit.Literature.CondP001g14

/-! Bernoulli triangular rows, moving CDF thresholds, and random binomial parameters. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
open scoped BoundedContinuousFunction
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace AronowAudit.P001.TailA

universe u
local instance instDecidableBernoulliRows (p : Prop) : Decidable p := Classical.propDecidable p

/-- The bounded-test and probability-measure formulations agree for measurable rows. -/
theorem bernoulliRows_rowWeak_iff
    {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {Z : ∀ n, Ω n → ℝ} {G : Measure ℝ} [IsProbabilityMeasure G]
    (hZ : ∀ n, AEMeasurable (Z n) (μ n)) :
    AronowAudit.Literature.RowWeak μ Z G ↔
      TendstoInDistribution Z atTop id μ G := by
  rw [tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hZ aemeasurable_id]
  constructor
  · intro h f
    exact h f f.continuous ⟨‖f‖, fun x => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x⟩
  · intro h f hf ⟨C, hC⟩
    let g : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * C)
      (fun x y => by
        rw [Real.dist_eq]
        have hxy : |f x - f y| ≤ |f x| + |f y| := by
          simpa using abs_sub_le (f x) 0 (f y)
        exact hxy.trans (by linarith [hC x, hC y]))
    exact h g

/-- The indicator associated with a Boolean observation has the specified mean and variance. -/
theorem bernoulliRows_indicator_moments {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Ω → Bool) (hB : Measurable B) :
    let Y := fun ω => if B ω then (1 : ℝ) else 0
    let p := prob μ {ω | B ω = true}
    (∫ ω, Y ω ∂μ) = p ∧ variance Y μ = p * (1 - p) := by
  dsimp
  let Y : Ω → ℝ := fun ω => if B ω then 1 else 0
  have hm : Measurable Y := (Measurable.of_discrete (f := fun b : Bool =>
    if b then (1 : ℝ) else 0)).comp hB
  have he : (∫ ω, Y ω ∂μ) = prob μ {ω | B ω = true} := by
    have hs : MeasurableSet {ω | B ω = true} := hB (measurableSet_singleton true)
    simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, prob, Measure.real] using
      (integral_indicator_one (μ := μ) hs)
  have hL : MemLp Y 2 μ := MemLp.of_bound hm.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by cases h : B ω <;> simp [Y, h])
  have hsq : Y ^ 2 = Y := by
    funext ω
    cases h : B ω <;> simp [Y, h]
  exact ⟨he, by rw [variance_eq_sub hL, hsq, he]; ring⟩

/-- Bernoulli row convergence in Mathlib's distribution formulation. -/
theorem bernoulliRows_tendstoInDistribution
    (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (B : ∀ n, Fin (m n) → Ω n → Bool) (p : ℕ → ℝ) (p0 : ℝ)
    (hB : ∀ n i, Measurable (B n i)) (hi : ∀ n, iIndepFun (B n) (μ n))
    (hp : ∀ n i, prob (μ n) {ω | B n i ω = true} = p n)
    (hp0 : 0 < p0 ∧ p0 < 1) (hplim : Tendsto p atTop (nhds p0)) :
    TendstoInDistribution
      (fun n ω => ((∑ i, if B n i ω then (1 : ℝ) else 0) - (m n : ℝ) * p n) /
        Real.sqrt (m n)) atTop (id : ℝ → ℝ) μ
      (gaussianReal 0 ⟨p0 * (1 - p0), mul_nonneg hp0.1.le (sub_nonneg.mpr hp0.2.le)⟩) := by
  let v : ℝ := p0 * (1 - p0)
  let σ : ℝ := Real.sqrt v
  have hv : 0 < v := mul_pos hp0.1 (sub_pos.mpr hp0.2)
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  have hσsq : σ ^ 2 = v := Real.sq_sqrt hv.le
  let Y := fun n (i : Fin (m n)) (ω : Ω n) => if B n i ω then (1 : ℝ) else 0
  let c := fun n => (Real.sqrt (m n) * σ)⁻¹
  let W := fun n (i : Fin (m n)) (ω : Ω n) => c n * (Y n i ω - p n)
  have hY : ∀ n i, Measurable (Y n i) := fun n i =>
    (Measurable.of_discrete (f := fun b : Bool => if b then (1 : ℝ) else 0)).comp (hB n i)
  have hmom : ∀ n i, (∫ ω, Y n i ω ∂μ n) = p n ∧
      variance (Y n i) (μ n) = p n * (1 - p n) := by
    intro n i
    simpa only [hp n i] using bernoulliRows_indicator_moments (μ n) (B n i) (hB n i)
  have hYL : ∀ n i, Integrable (Y n i) (μ n) := fun n i =>
    Integrable.of_bound (hY n i).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by cases h : B n i ω <;> simp [Y, h])
  have hmeas : ∀ n i, Measurable (W n i) := fun n i =>
    ((hY n i).sub measurable_const).const_mul _
  have hindep : ∀ n, iIndepFun (W n) (μ n) := by
    intro n
    exact (hi n).comp (fun _ b => c n * ((if b then (1 : ℝ) else 0) - p n))
      (fun _ => Measurable.of_discrete)
  have hmean : ∀ n i, (∫ ω, W n i ω ∂μ n) = 0 := by
    intro n i
    dsimp only [W]
    rw [integral_const_mul, integral_sub (hYL n i) (integrable_const _),
      (hmom n i).1, integral_const]
    simp
  have hvar : ∀ n i, variance (W n i) (μ n) = c n ^ 2 * (p n * (1 - p n)) := by
    intro n i
    rw [show W n i = fun ω => c n * (Y n i ω - p n) from rfl,
      variance_const_mul, variance_sub_const (hY n i).aestronglyMeasurable, (hmom n i).2]
  have hmpos : ∀ᶠ n in atTop, 0 < m n := hm.eventually (eventually_gt_atTop 0)
  have hsumvar : ∀ᶠ n in atTop, (∑ i, variance (W n i) (μ n)) = p n * (1 - p n) / v := by
    filter_upwards [hmpos] with n hn
    simp only [hvar, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp only [c]
    simp only [mul_inv_rev, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg (m n)), hσsq]
    have hmn : (m n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
    <;> ring
  have hvarlim : Tendsto (fun n => ∑ i, variance (W n i) (μ n)) atTop (𝓝 1) := by
    have h : Tendsto (fun n => p n * (1 - p n) / v) atTop (𝓝 (p0 * (1 - p0) / v)) :=
      (hplim.mul (tendsto_const_nhds.sub hplim)).div_const v
    have he : p0 * (1 - p0) / v = 1 := div_self hv.ne'
    simpa only [he] using h.congr' (show
      (fun n => p n * (1 - p n) / v) =ᶠ[atTop] (fun n => ∑ i, variance (W n i) (μ n)) from by
        filter_upwards [hsumvar] with n hn
        exact hn.symm)
  have hbdd : ∀ n i ω, |W n i ω| ≤ c n := by
    intro n i ω
    have hpn : 0 ≤ p n ∧ p n ≤ 1 := by
      rw [← hp n i]
      exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩
    have hc : 0 ≤ c n := by dsimp [c]; positivity
    have hYb : |Y n i ω - p n| ≤ 1 := by
      cases h : B n i ω <;> simp only [Y, h, Bool.false_eq_true, ↓reduceIte]
      · rw [zero_sub, abs_neg, abs_of_nonneg hpn.1]; exact hpn.2
      · rw [abs_of_nonneg (sub_nonneg.mpr hpn.2)]; linarith [hpn.1]
    dsimp only [W]
    rw [abs_mul, abs_of_nonneg hc]
    simpa using mul_le_mul_of_nonneg_left hYb hc
  have hc : Tendsto c atTop (𝓝 0) := by
    have hmtop : Tendsto (fun n => (m n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hm
    have hi0 := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hmtop)
    simpa [c, mul_inv_rev] using (tendsto_const_nhds.mul hi0 :
      Tendsto (fun n => σ⁻¹ * (Real.sqrt (m n))⁻¹) atTop (𝓝 (σ⁻¹ * 0)))
  have hclt := AronowAudit.P037.LindebergCompletion.lindeberg_clt_of_bounded
    (P := μ) (P' := gaussianReal 0 1) (Z := id) hmeas hindep hmean hvarlim hbdd hc
    (show HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) from
      ⟨aemeasurable_id, Measure.map_id⟩)
  have hscaled := hclt.continuous_comp (g := fun z : ℝ => σ * z) (by fun_prop)
  have hsum : ∀ n ω, σ * (∑ i, W n i ω) =
      ((∑ i, if B n i ω then (1 : ℝ) else 0) - (m n : ℝ) * p n) /
        Real.sqrt (m n) := by
    intro n ω
    simp only [W, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp only [c, Y]
    rw [mul_inv_rev]
    field_simp [hσ.ne']
  have hlaw : (gaussianReal 0 1).map (fun z : ℝ => σ * z) =
      gaussianReal 0 ⟨v, hv.le⟩ := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply Subtype.ext
      simpa using hσsq
  refine ⟨?_, aemeasurable_id, ?_⟩
  · intro n
    simpa only [Function.comp_def, hsum] using hscaled.forall_aemeasurable n
  · simpa only [Function.comp_def, id_eq, hsum, hlaw, Measure.map_id, v] using hscaled.tendsto

theorem bernoulli_row_weak
    (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (B : ∀ n, Fin (m n) → Ω n → Bool) (p : ℕ → ℝ) (p0 : ℝ)
    (hB : ∀ n i, Measurable (B n i)) (hi : ∀ n, iIndepFun (B n) (μ n))
    (hp : ∀ n i, prob (μ n) {ω | B n i ω = true} = p n)
    (hp0 : 0 < p0 ∧ p0 < 1) (hplim : Tendsto p atTop (nhds p0)) :
    AronowAudit.Literature.RowWeak μ
      (fun n ω => ((∑ i, if B n i ω then (1 : ℝ) else 0) - (m n : ℝ)*p n) /
        Real.sqrt (m n))
      (gaussianReal 0 ⟨p0*(1-p0), mul_nonneg hp0.1.le (sub_nonneg.mpr hp0.2.le)⟩) := by
  have h := bernoulliRows_tendstoInDistribution Ω μ m hm B p p0 hB hi hp hp0 hplim
  exact (bernoulliRows_rowWeak_iff h.forall_aemeasurable).mpr h

/-- A real probability measure without atoms has a continuous CDF. -/
theorem bernoulliRows_cdf_continuous (G : Measure ℝ) [IsProbabilityMeasure G]
    [NullSingletonClass G] : Continuous (fun t => prob G (Set.Iic t)) := by
  have he : (fun t => prob G (Set.Iic t)) = ProbabilityTheory.cdf G := by
    funext t
    exact (ProbabilityTheory.cdf_eq_real G t).symm
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (ProbabilityTheory.cdf G).mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [(ProbabilityTheory.cdf G).rightLim_eq]
  have hz := (ProbabilityTheory.cdf G).measure_singleton x
  rw [ProbabilityTheory.measure_cdf, measure_singleton] at hz
  have hle := ENNReal.ofReal_eq_zero.mp hz.symm
  exact le_antisymm ((ProbabilityTheory.cdf G).mono.leftLim_le le_rfl) (by linarith)

/-- Weakly converging measurable rows have converging CDFs at every atom-free threshold. -/
theorem bernoulliRows_cdf_of_distribution
    {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {Z : ∀ n, Ω n → ℝ} {G : Measure ℝ} [IsProbabilityMeasure G]
    (h : TendstoInDistribution Z atTop id μ G) (t : ℝ) (ht : G {t} = 0) :
    Tendsto (fun n => prob (μ n) {ω | Z n ω ≤ t}) atTop (𝓝 (prob G (Set.Iic t))) := by
  have hf : G.map (id : ℝ → ℝ) (frontier (Set.Iic t)) = 0 := by
    simpa only [Measure.map_id, frontier_Iic] using ht
  have hc := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h.tendsto hf
  have hc' : Tendsto (fun n => (μ n).map (Z n) (Set.Iic t)) atTop (𝓝 (G (Set.Iic t))) := by
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using hc
  have hr := (ENNReal.tendsto_toReal (measure_ne_top G (Set.Iic t))).comp hc'
  simpa only [Function.comp_def, ProbabilityMeasure.coe_mk, Measure.map_id,
    Measure.map_apply_of_aemeasurable (h.forall_aemeasurable _ ) measurableSet_Iic,
    Set.preimage, Set.mem_Iic, prob] using hr

/-- A sandwich of threshold events suffices for moving-cutoff convergence. -/
theorem bernoulliRows_moving_event
    {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {Z : ∀ n, Ω n → ℝ} {G : Measure ℝ} [IsProbabilityMeasure G]
    {x : ℝ} (hcont : ContinuousAt (fun t => prob G (Set.Iic t)) x)
    (hCDF : ∀ t, Tendsto (fun n => prob (μ n) {ω | Z n ω ≤ t}) atTop
      (𝓝 (prob G (Set.Iic t)))) (A : ∀ n, Set (Ω n))
    (hlo : ∀ b < x, ∀ᶠ n in atTop, {ω | Z n ω ≤ b} ⊆ A n)
    (hhi : ∀ b > x, ∀ᶠ n in atTop, A n ⊆ {ω | Z n ω ≤ b}) :
    Tendsto (fun n => prob (μ n) (A n)) atTop (𝓝 (prob G (Set.Iic x))) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp
      (hcont.eventually (eventually_gt_nhds ha))
    have hdist : dist (x - δ / 2) x < δ := by
      rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hδ)]
      linarith
    have hb : a < prob G (Set.Iic (x - δ / 2)) := hd hdist
    filter_upwards [(hCDF (x - δ / 2)).eventually (eventually_gt_nhds hb),
      hlo (x - δ / 2) (by linarith)] with n hn hsub
    exact hn.trans_le (measureReal_mono hsub)
  · intro a ha
    obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp
      (hcont.eventually (eventually_lt_nhds ha))
    have hdist : dist (x + δ / 2) x < δ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
      linarith
    have hb : prob G (Set.Iic (x + δ / 2)) < a := hd hdist
    filter_upwards [(hCDF (x + δ / 2)).eventually (eventually_lt_nhds hb),
      hhi (x + δ / 2) (by linarith)] with n hn hsub
    exact lt_of_le_of_lt (measureReal_mono hsub) hn

/-- Both weak and strict moving thresholds have the same continuous limiting CDF. -/
theorem row_weak_moving_cdf
    {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {Z : ∀ n, Ω n → ℝ} {G : Measure ℝ} [IsProbabilityMeasure G] [NullSingletonClass G]
    (hZ : ∀ n, AEMeasurable (Z n) (μ n))
    (h : AronowAudit.Literature.RowWeak μ Z G)
    (t : ℕ → ℝ) (x : ℝ) (ht : Tendsto t atTop (𝓝 x)) :
    Tendsto (fun n => prob (μ n) {ω | Z n ω ≤ t n}) atTop (𝓝 (prob G (Set.Iic x))) ∧
    Tendsto (fun n => prob (μ n) {ω | Z n ω < t n}) atTop (𝓝 (prob G (Set.Iic x))) := by
  have hd := (bernoulliRows_rowWeak_iff hZ).mp h
  have hc := (bernoulliRows_cdf_continuous G).continuousAt (x := x)
  have hCDF := fun b => bernoulliRows_cdf_of_distribution hd b (measure_singleton b)
  constructor
  · apply bernoulliRows_moving_event hc hCDF
    · intro b hb
      filter_upwards [ht.eventually (eventually_gt_nhds hb)] with n hn ω hω
      exact hω.trans hn.le
    · intro b hb
      filter_upwards [ht.eventually (eventually_lt_nhds hb)] with n hn ω hω
      exact hω.trans hn.le
  · apply bernoulliRows_moving_event hc hCDF
    · intro b hb
      filter_upwards [ht.eventually (eventually_gt_nhds hb)] with n hn ω hω
      exact hω.trans_lt hn
    · intro b hb
      filter_upwards [ht.eventually (eventually_lt_nhds hb)] with n hn ω hω
      exact hω.le.trans hn.le

/-- CDF of a centered binomial count, using the `sqrt n` normalization. -/
def binomialCountCDF (n : ℕ) (p : unitInterval) (t : ℝ) : ℝ :=
  prob (binomial n p) {k | ((k : ℝ) - (n : ℝ) * (p : ℝ)) / Real.sqrt n ≤ t}

/-- The strict version is useful for complements of lattice upper tails. -/
def binomialCountStrictCDF (n : ℕ) (p : unitInterval) (t : ℝ) : ℝ :=
  prob (binomial n p) {k | ((k : ℝ) - (n : ℝ) * (p : ℝ)) / Real.sqrt n < t}

/-- Deterministic varying parameters and varying thresholds, including strict lattice events. -/
theorem binomial_moving_cdf (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (p : ℕ → unitInterval) (p0 : ℝ) (hp0 : 0 < p0 ∧ p0 < 1)
    (hp : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 p0))
    (t : ℕ → ℝ) (x : ℝ) (ht : Tendsto t atTop (𝓝 x)) :
    let G := gaussianReal 0 ⟨p0 * (1 - p0), mul_nonneg hp0.1.le (sub_nonneg.mpr hp0.2.le)⟩
    Tendsto (fun n => binomialCountCDF (m n) (p n) (t n)) atTop (𝓝 (prob G (Set.Iic x))) ∧
    Tendsto (fun n => binomialCountStrictCDF (m n) (p n) (t n)) atTop (𝓝 (prob G (Set.Iic x))) := by
  let P := fun n => Measure.pi (fun _ : Fin (m n) => bernoulliMeasure true false (p n))
  let B := fun n (i : Fin (m n)) (ω : Fin (m n) → Bool) => ω i
  have hB : ∀ n i, Measurable (B n i) := fun n i => measurable_pi_apply i
  have hi : ∀ n, iIndepFun (B n) (P n) := fun n => iIndepFun_pi
    (fun _ : Fin (m n) => aemeasurable_id)
  have htrue : ∀ n, (bernoulliMeasure true false (p n)).real {true} = (p n : ℝ) := by
    intro n
    simp [bernoulliMeasure_real_apply]
  have hpB : ∀ n i, prob (P n) {ω | B n i ω = true} = (p n : ℝ) := by
    intro n i
    have hh := congrArg (fun ν : Measure Bool => ν.real {true})
      (measurePreserving_eval (fun _ : Fin (m n) => bernoulliMeasure true false (p n)) i).map_eq
    rw [map_measureReal_apply (measurable_pi_apply i) (measurableSet_singleton true)] at hh
    exact hh.trans (htrue n)
  have hc : ∀ n, (P n).map (fun ω =>
      (Finset.univ.filter (fun i => ω i = true)).card) = binomial (m n) (p n) := by
    intro n
    have hh := finite_bootstrap_iid_count_law (bernoulliMeasure true false (p n))
      {true} (measurableSet_singleton true) (m n)
    have he : (⟨(bernoulliMeasure true false (p n)).real {true}, by simp⟩ : unitInterval) = p n :=
      Subtype.ext (htrue n)
    simpa only [P, Set.mem_singleton_iff, he] using hh
  have hsum : ∀ n (ω : Fin (m n) → Bool),
      (∑ i, if B n i ω then (1 : ℝ) else 0) =
        ((Finset.univ.filter (fun i => ω i = true)).card : ℝ) := by
    intro n ω
    rw [Finset.card_filter]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rfl
  have hw := bernoulli_row_weak (fun n => Fin (m n) → Bool) P m hm B
    (fun n => (p n : ℝ)) p0 hB hi hpB hp0 hp
  have hZ : ∀ n, Measurable (fun ω =>
      ((∑ i, if B n i ω then (1 : ℝ) else 0) - (m n : ℝ) * (p n : ℝ)) / Real.sqrt (m n)) := by
    intro n
    exact ((Finset.univ.measurable_sum fun i _ =>
      (Measurable.of_discrete (f := fun b : Bool => if b then (1 : ℝ) else 0)).comp
        (hB n i)).sub measurable_const).div_const _
  have hv : (⟨p0 * (1 - p0), mul_nonneg hp0.1.le (sub_nonneg.mpr hp0.2.le)⟩ : ℝ≥0) ≠ 0 := by
    exact ne_of_gt (show (0 : ℝ≥0) <
      ⟨p0 * (1 - p0), mul_nonneg hp0.1.le (sub_nonneg.mpr hp0.2.le)⟩ from
      mul_pos hp0.1 (sub_pos.mpr hp0.2))
  letI instNullGaussianBinomial : NullSingletonClass
      (gaussianReal 0 ⟨p0 * (1 - p0), mul_nonneg hp0.1.le (sub_nonneg.mpr hp0.2.le)⟩) :=
    nullSingletonClass_gaussianReal hv
  have hh := row_weak_moving_cdf (fun n => (hZ n).aemeasurable) hw t x ht
  have he : ∀ n, prob (P n) {ω |
      ((∑ i, if B n i ω then (1 : ℝ) else 0) - (m n : ℝ) * (p n : ℝ)) / Real.sqrt (m n) ≤ t n} =
        binomialCountCDF (m n) (p n) (t n) := by
    intro n
    unfold binomialCountCDF
    rw [← hc n]
    simp only [prob, Measure.map_apply Measurable.of_discrete (MeasurableSet.of_discrete)]
    congr 2
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hsum]
  have he' : ∀ n, prob (P n) {ω |
      ((∑ i, if B n i ω then (1 : ℝ) else 0) - (m n : ℝ) * (p n : ℝ)) / Real.sqrt (m n) < t n} =
        binomialCountStrictCDF (m n) (p n) (t n) := by
    intro n
    unfold binomialCountStrictCDF
    rw [← hc n]
    simp only [prob, Measure.map_apply Measurable.of_discrete (MeasurableSet.of_discrete)]
    congr 2
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hsum]
  exact ⟨by simpa only [he] using hh.1, by simpa only [he'] using hh.2⟩

/-- Finite-sum formulas make the parameter and the moving cutoff jointly measurable. -/
theorem binomial_count_cdf_measurable {E : Type u} [MeasurableSpace E]
    (n : ℕ) (p : E → unitInterval) (t : E → ℝ) (hp : Measurable p) (ht : Measurable t) :
    Measurable (fun z => binomialCountCDF n (p z) (t z)) ∧
    Measurable (fun z => binomialCountStrictCDF n (p z) (t z)) := by
  have hformula : ∀ q : unitInterval, ∀ a : ℝ,
      binomialCountCDF n q a = ∑ k ∈ Finset.Iic n,
        (n.choose k : ℝ) * (q : ℝ) ^ k * (1 - (q : ℝ)) ^ (n - k) *
          (if ((k : ℝ) - (n : ℝ) * (q : ℝ)) / Real.sqrt n ≤ a then 1 else 0) := by
    intro q a
    change (binomial n q).real _ = _
    rw [← integral_indicator_one (μ := binomial n q) MeasurableSet.of_discrete, integral_binomial]
    simp [Set.indicator, smul_eq_mul]
  have hformula' : ∀ q : unitInterval, ∀ a : ℝ,
      binomialCountStrictCDF n q a = ∑ k ∈ Finset.Iic n,
        (n.choose k : ℝ) * (q : ℝ) ^ k * (1 - (q : ℝ)) ^ (n - k) *
          (if ((k : ℝ) - (n : ℝ) * (q : ℝ)) / Real.sqrt n < a then 1 else 0) := by
    intro q a
    change (binomial n q).real _ = _
    rw [← integral_indicator_one (μ := binomial n q) MeasurableSet.of_discrete, integral_binomial]
    simp [Set.indicator, smul_eq_mul]
  have hpr : Measurable (fun z => (p z : ℝ)) := measurable_subtype_coe.comp hp
  constructor
  · simp only [hformula]
    apply Finset.measurable_sum
    intro k hk
    apply Measurable.mul
    · fun_prop
    · exact Measurable.ite (measurableSet_le
        ((measurable_const.sub (hpr.const_mul _)).div_const _) ht) measurable_const measurable_const
  · simp only [hformula']
    apply Finset.measurable_sum
    intro k hk
    apply Measurable.mul
    · fun_prop
    · exact Measurable.ite (measurableSet_lt
        ((measurable_const.sub (hpr.const_mul _)).div_const _) ht) measurable_const measurable_const

/-- The deterministic row theorem applies to parameters and cutoffs converging in probability.
The proof extracts a common almost-sure subsequence of the two inputs. -/
theorem random_binomial_moving_cdf {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (p : ℕ → Ω → unitInterval) (p0 : ℝ) (hp0 : 0 < p0 ∧ p0 < 1)
    (hpmeas : ∀ n, Measurable (p n)) (hp : CP μ (fun n ω => (p n ω : ℝ)) p0)
    (t : ℕ → Ω → ℝ) (x : ℝ) (htmeas : ∀ n, Measurable (t n)) (ht : CP μ t x) :
    let G := gaussianReal 0 ⟨p0 * (1 - p0), mul_nonneg hp0.1.le (sub_nonneg.mpr hp0.2.le)⟩
    CP μ (fun n ω => binomialCountCDF (m n) (p n ω) (t n ω)) (prob G (Set.Iic x)) ∧
    CP μ (fun n ω => binomialCountStrictCDF (m n) (p n ω) (t n ω)) (prob G (Set.Iic x)) := by
  have hp' : TendstoInMeasure μ (fun n ω => (p n ω : ℝ)) atTop (fun _ => p0) :=
    tendstoInMeasure_iff_measureReal_dist.mpr hp
  have ht' : TendstoInMeasure μ t atTop (fun _ => x) :=
    tendstoInMeasure_iff_measureReal_dist.mpr ht
  have hgeneral : ∀ (F : ℕ → Ω → ℝ), (∀ n, AEStronglyMeasurable (F n) μ) →
      (∀ (ns : ℕ → ℕ), StrictMono ns →
        ∀ᵐ ω ∂μ, Tendsto (fun k => (p (ns k) ω : ℝ)) atTop (𝓝 p0) →
          Tendsto (fun k => t (ns k) ω) atTop (𝓝 x) →
          Tendsto (fun k => F (ns k) ω) atTop
            (𝓝 (prob (gaussianReal 0
              ⟨p0 * (1 - p0), mul_nonneg hp0.1.le (sub_nonneg.mpr hp0.2.le)⟩) (Set.Iic x)))) →
      CP μ F (prob (gaussianReal 0
        ⟨p0 * (1 - p0), mul_nonneg hp0.1.le (sub_nonneg.mpr hp0.2.le)⟩) (Set.Iic x)) := by
    intro F hF hlim
    apply tendstoInMeasure_iff_measureReal_dist.mp
    apply (exists_seq_tendstoInMeasure_atTop_iff hF).mpr
    intro ns hns
    obtain ⟨a, ha, hpa⟩ := (hp'.comp hns.tendsto_atTop).exists_seq_tendsto_ae
    obtain ⟨b, hb, htb⟩ := (ht'.comp (hns.comp ha).tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨a ∘ b, ha.comp hb, ?_⟩
    filter_upwards [hpa, htb, hlim (ns ∘ a ∘ b) (hns.comp (ha.comp hb))] with ω hpω htω hω
    exact hω (hpω.comp hb.tendsto_atTop) htω
  constructor
  · apply hgeneral
    · intro n
      exact ((binomial_count_cdf_measurable (m n) (p n) (t n) (hpmeas n) (htmeas n)).1).aestronglyMeasurable
    · intro ns hns
      exact ae_of_all _ fun ω hpω htω => (binomial_moving_cdf
        (m ∘ ns) (hm.comp hns.tendsto_atTop) (fun k => p (ns k) ω) p0 hp0 hpω
        (fun k => t (ns k) ω) x htω).1
  · apply hgeneral
    · intro n
      exact ((binomial_count_cdf_measurable (m n) (p n) (t n) (hpmeas n) (htmeas n)).2).aestronglyMeasurable
    · intro ns hns
      exact ae_of_all _ fun ω hpω htω => (binomial_moving_cdf
        (m ∘ ns) (hm.comp hns.tendsto_atTop) (fun k => p (ns k) ω) p0 hp0 hpω
        (fun k => t (ns k) ω) x htω).2

end AronowAudit.P001.TailA
