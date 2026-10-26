import AronowAudit.Shared.MapTailB.QuantileBridge
import AronowAudit.P022.Wave1.Gap.GP022B1b
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Topology.Order.Monotone

/-! Quantile convergence on the fixed uniform level space. -/

open MeasureTheory ProbabilityTheory Causalean.Stat Set Filter
open scoped Topology ENNReal NNReal BigOperators
open AronowAudit.P022 AronowAudit.P022.Wave1

noncomputable section

/-- Pointwise CDF convergence implies inverse convergence at continuity levels.
No condition on the atoms or on the left CDF values is needed. -/
theorem TailB_quantile_tendsto_at_continuity
    (μn : ℕ → Measure ℝ) (μ : Measure ℝ)
    (hF : ∀ x, Tendsto (fun n => cdf (μn n) x) atTop (𝓝 (cdf μ x)))
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hQ : ContinuousWithinAt (quantile μ) (Ioo (0 : ℝ) 1) u) :
    Tendsto (fun n => quantile (μn n) u) atTop (𝓝 (quantile μ u)) := by
  have hc : ContinuousAt (quantile μ) u :=
    hQ.continuousAt (isOpen_Ioo.mem_nhds hu)
  apply tendsto_order.mpr
  constructor
  · intro x hx
    obtain ⟨δ, hδ, hδQ⟩ := Metric.continuousAt_iff.mp hc
      (quantile μ u - x) (sub_pos.mpr hx)
    let d := min (δ / 2) (u / 2)
    have hd : 0 < d := lt_min (half_pos hδ) (half_pos hu.1)
    have hdu : d ≤ u / 2 := min_le_right _ _
    have hdd : d < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ha0 : 0 < u - d := by linarith
    have ha1 : u - d < 1 := by linarith [hu.2]
    have hdist : dist (u - d) u < δ := by
      rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hd]
      exact hdd
    have hax : x < quantile μ (u - d) := by
      have hh := hδQ hdist
      rw [Real.dist_eq, abs_lt] at hh
      linarith [hh.1]
    have hFx : cdf μ x < u := by
      have hnot : ¬ u - d ≤ cdf μ x := by
        intro hh
        exact (not_le.mpr hax) (quantile_le_of_le_cdf ha0 hh)
      linarith [lt_of_not_ge hnot]
    filter_upwards [(hF x).eventually_lt_const hFx] with n hn
    exact lt_of_not_ge (fun hle => (not_le.mpr hn) (le_cdf_of_quantile_le hu.2 hle))
  · intro x hx
    obtain ⟨δ, hδ, hδQ⟩ := Metric.continuousAt_iff.mp hc
      (x - quantile μ u) (sub_pos.mpr hx)
    let d := min (δ / 2) ((1 - u) / 2)
    have hd : 0 < d := lt_min (half_pos hδ) (half_pos (sub_pos.mpr hu.2))
    have hdu : d ≤ (1 - u) / 2 := min_le_right _ _
    have hdd : d < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hb1 : u + d < 1 := by linarith
    have hdist : dist (u + d) u < δ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hd]
      exact hdd
    have hbx : quantile μ (u + d) < x := by
      have hh := hδQ hdist
      rw [Real.dist_eq, abs_lt] at hh
      linarith [hh.2]
    have hFx : u < cdf μ x := by
      have hh := (le_cdf_quantile (μ := μ) hb1).trans
        (monotone_cdf μ hbx.le)
      linarith
    obtain ⟨y, hyQ, hyx⟩ := exists_between hx
    -- A strict upper bracket is obtained at an intermediate point.
    have hyF : u < cdf μ y := by
      obtain ⟨δ', hδ', hδ'Q⟩ := Metric.continuousAt_iff.mp hc
        (y - quantile μ u) (sub_pos.mpr hyQ)
      let e := min (δ' / 2) ((1 - u) / 2)
      have he : 0 < e := lt_min (half_pos hδ') (half_pos (sub_pos.mpr hu.2))
      have he1 : u + e < 1 := by have := min_le_right (δ' / 2) ((1-u)/2); linarith
      have heδ : dist (u + e) u < δ' := by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos he]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hQy : quantile μ (u + e) < y := by
        have hh := hδ'Q heδ
        rw [Real.dist_eq, abs_lt] at hh
        linarith [hh.2]
      have hh := (le_cdf_quantile (μ := μ) he1).trans (monotone_cdf μ hQy.le)
      linarith
    filter_upwards [(hF y).eventually_const_lt hyF] with n hn
    exact lt_of_le_of_lt (quantile_le_of_le_cdf hu.1 hn.le) hyx

/-- Quantiles converge almost everywhere for the uniform level law, including
when the limiting distribution has atoms. -/
theorem TailB_quantile_tendsto_ae
    (μn : ℕ → Measure ℝ) (μ : Measure ℝ)
    (hF : ∀ x, Tendsto (fun n => cdf (μn n) x) atTop (𝓝 (cdf μ x))) :
    ∀ᵐ u ∂unifOI, Tendsto (fun n => quantile (μn n) u) atTop (𝓝 (quantile μ u)) := by
  have hc := (monotoneOn_quantile μ).countable_not_continuousWithinAt
  have hz : unifOI {u ∈ Ioo (0 : ℝ) 1 |
      ¬ContinuousWithinAt (quantile μ) (Ioo (0 : ℝ) 1) u} = 0 :=
    (Measure.restrict_le_self _).trans_eq (hc.measure_zero volume) |>.antisymm (by positivity)
  have hgood : ∀ᵐ u ∂unifOI, u ∉ {u ∈ Ioo (0 : ℝ) 1 |
      ¬ContinuousWithinAt (quantile μ) (Ioo (0 : ℝ) 1) u} := by
    simpa only [ae_iff, not_not, Set.mem_setOf_eq] using hz
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo, hgood] with u hu hg
  exact TailB_quantile_tendsto_at_continuity μn μ hF hu (by simpa [hu] using hg)

/-- Vitali on the fixed level space also supplies the limiting second moment. -/
theorem TailB_quantile_L2_of_uniformIntegrable
    (μn : ℕ → Measure ℝ) (μ : Measure ℝ)
    (hF : ∀ x, Tendsto (fun n => cdf (μn n) x) atTop (𝓝 (cdf μ x)))
    (hUI : UniformIntegrable (fun n => quantile (μn n)) 2 unifOI) :
    MemLp (quantile μ) 2 unifOI ∧
      Tendsto (fun n => eLpNorm (quantile (μn n) - quantile μ) 2 unifOI) atTop (𝓝 0) := by
  have ha := TailB_quantile_tendsto_ae μn μ hF
  have hm := hUI.memLp_of_ae_tendsto ha
  exact ⟨hm, tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => (aemeasurable_quantile_unifOI (μn n)).aestronglyMeasurable) hm hUI.1 ha⟩

/-- The square of the extended L2 seminorm is the nonnegative square integral. -/
theorem TailB_eLpNorm_two_sq {α : Type*} [MeasurableSpace α] {m : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 m) :
    eLpNorm f 2 m ^ (2 : ℕ) = ENNReal.ofReal (∫ x, f x ^ 2 ∂m) := by
  have hh := eLpNorm_nnreal_pow_eq_lintegral (μ := m) (p := (2 : ℝ≥0))
    (by norm_num) hf.aestronglyMeasurable
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at hh
  rw [hh, ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (ae_of_all _ (fun x => sq_nonneg (f x)))]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm]
  simp only [Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg (f x)), sq_abs]

/-- A square-tail criterion for L2 uniform integrability, expressed in real
integrals so that it applies directly to finite averages. -/
theorem TailB_uniformIntegrable_two_of_square_tails
    {α ι : Type*} [MeasurableSpace α] {m : Measure α} [IsFiniteMeasure m]
    (f : ι → α → ℝ) (hf : ∀ i, MemLp (f i) 2 m)
    (htail : ∀ ε > 0, ∃ C : ℝ≥0, ∀ i,
      (∫ x, if (C : ℝ) ≤ |f i x| then f i x ^ 2 else 0 ∂m) ≤ ε) :
    UniformIntegrable f 2 m := by
  apply uniformIntegrable_of (by norm_num) (by norm_num)
    (fun i => (hf i).aestronglyMeasurable)
  intro ε hε
  by_cases htop : ε = ∞
  · subst ε
    exact ⟨0, fun _ => le_top⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨C, hC⟩ := htail (ε.toReal ^ 2) (sq_pos_of_pos he)
  refine ⟨C, fun i => ?_⟩
  let A : Set α := {x | C ≤ ‖f i x‖₊}
  have hA : NullMeasurableSet A m :=
    nullMeasurableSet_le aemeasurable_const (hf i).aemeasurable.nnnorm
  have hfi : MemLp (A.indicator (f i)) 2 m :=
    (hf i).of_le ((hf i).aestronglyMeasurable.indicator₀ hA)
      (ae_of_all _ (fun x => by
        by_cases hx : x ∈ A <;> simp [Set.indicator, hx]))
  have hsquare : (fun x => (A.indicator (f i) x) ^ 2) =
      (fun x => if (C : ℝ) ≤ |f i x| then f i x ^ 2 else 0) := by
    funext x
    have he : C ≤ ‖f i x‖₊ ↔ (C : ℝ) ≤ |f i x| := by
      exact_mod_cast (show (C : ℝ) ≤ ‖f i x‖ ↔ (C : ℝ) ≤ |f i x| by rfl)
    simp [A, Set.indicator, he]
  have hbound : eLpNorm (A.indicator (f i)) 2 m ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) := by
    rw [TailB_eLpNorm_two_sq hfi, hsquare]
    calc
      _ ≤ ENNReal.ofReal (ε.toReal ^ 2) := ENNReal.ofReal_le_ofReal (hC i)
      _ = ε ^ (2 : ℕ) := by rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal htop]
  exact (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hbound

/-- The quantile law transports any measurable integrand, with totalized
integrals on both sides. -/
theorem TailB_integral_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ u, f (quantile μ u) ∂unifOI) = ∫ x, f x ∂μ := by
  conv_rhs => rw [← quantile_map_uniform μ]
  exact (integral_map (aemeasurable_quantile_unifOI μ)
    hf.aestronglyMeasurable).symm

/-- Finite empirical quantiles have finite second moments. -/
theorem TailB_empirical_quantile_memLp {N : ℕ} [NeZero N] (y : Fin N → ℝ) :
    MemLp (quantile (TailB_empiricalLaw y : Measure ℝ)) 2 unifOI := by
  have hfin : MemLp y 2 (SharpBounds.unitLaw N : Measure (Fin N)) := by
    obtain ⟨C, hC⟩ := (Set.finite_range (fun i => ‖y i‖)).bddAbove
    apply MemLp.of_bound (measurable_of_finite y).aestronglyMeasurable C
    exact ae_of_all _ (fun i => hC (Set.mem_range_self i))
  have hmap : MemLp (fun x : ℝ => x) 2 (TailB_empiricalLaw y : Measure ℝ) := by
    exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      (measurable_of_finite y).aemeasurable).mpr hfin
  rw [← quantile_map_uniform (TailB_empiricalLaw y : Measure ℝ)] at hmap
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (aemeasurable_quantile_unifOI _)).mp hmap

/-- Finite empirical quantile integration is the exact finite average. -/
theorem TailB_integral_empirical_quantile {N : ℕ} [NeZero N] (y : Fin N → ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ u, f (quantile (TailB_empiricalLaw y : Measure ℝ) u) ∂unifOI) =
      AronowAudit.P022.finiteMean (fun i => f (y i)) := by
  rw [TailB_integral_quantile _ f hf, TailB_integral_empiricalLaw y f hf]

/-- A finite triangular array's uniform square tails transfer to its quantiles
without changing the base measure. -/
theorem TailB_finite_quantile_uniformIntegrable
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (y : (n : ℕ) → Fin (N n) → ℝ)
    (htail : ∀ ε > 0, ∃ β : ℝ, 1 < β ∧ ∀ n,
      AronowAudit.P022.finiteMean (fun i => if β ≤ y n i ^ 2 then y n i ^ 2 else 0) ≤ ε) :
    UniformIntegrable (fun n => quantile (TailB_empiricalLaw (y n) : Measure ℝ)) 2 unifOI := by
  apply TailB_uniformIntegrable_two_of_square_tails _
    (fun n => TailB_empirical_quantile_memLp (y n))
  intro ε hε
  obtain ⟨β, hβ, hb⟩ := htail ε hε
  refine ⟨⟨β, by linarith⟩, fun n => ?_⟩
  change (∫ u, (fun x : ℝ => if β ≤ |x| then x ^ 2 else 0)
    (quantile (TailB_empiricalLaw (y n) : Measure ℝ) u) ∂unifOI) ≤ ε
  have hmeas : Measurable (fun x : ℝ => if β ≤ |x| then x ^ 2 else 0) :=
    Measurable.ite (measurableSet_le measurable_const measurable_id.abs)
      (measurable_id.pow_const 2) measurable_const
  rw [TailB_integral_empirical_quantile (y n) _ hmeas]
  apply le_trans _ (hb n)
  apply Finset.expect_le_expect
  intro i _
  by_cases hy : β ≤ |y n i|
  · have hs : β ≤ y n i ^ 2 := by
      have := sq_abs (y n i)
      nlinarith [abs_nonneg (y n i)]
    simp [hy, hs]
  · simp only [hy, if_false]
    split_ifs <;> positivity

/-- Deterministic finite-population L2 quantile convergence, with a finite-tail
hypothesis and pointwise CDF convergence. -/
theorem TailB_finite_quantile_L2
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (y : (n : ℕ) → Fin (N n) → ℝ)
    (μ : Measure ℝ)
    (hF : ∀ x, Tendsto (fun n => AronowAudit.P022.empiricalCDF (y n) x)
      atTop (𝓝 (cdf μ x)))
    (htail : ∀ ε > 0, ∃ β : ℝ, 1 < β ∧ ∀ n,
      AronowAudit.P022.finiteMean (fun i => if β ≤ y n i ^ 2 then y n i ^ 2 else 0) ≤ ε) :
    MemLp (quantile μ) 2 unifOI ∧
      Tendsto (fun n => eLpNorm
        (quantile (TailB_empiricalLaw (y n) : Measure ℝ) - quantile μ) 2 unifOI)
        atTop (𝓝 0) := by
  apply TailB_quantile_L2_of_uniformIntegrable
    (fun n => (TailB_empiricalLaw (y n) : Measure ℝ)) μ
  · simpa only [TailB_cdf_empiricalLaw] using hF
  · exact TailB_finite_quantile_uniformIntegrable N y htail

/-- Square-tail integrability needs only L2, including for a.e. measurable functions. -/
theorem TailB_square_tail_integrable {α : Type*} [MeasurableSpace α]
    {m : Measure α} {f : α → ℝ} (hf : MemLp f 2 m) (β : ℝ) :
    Integrable (fun x => if β ≤ f x ^ 2 then f x ^ 2 else 0) m := by
  have hm : Measurable (fun x : ℝ => if β ≤ x ^ 2 then x ^ 2 else 0) :=
    Measurable.ite (measurableSet_le measurable_const (measurable_id.pow_const 2))
      (measurable_id.pow_const 2) measurable_const
  apply hf.integrable_sq.mono' (hm.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    dsimp [Function.comp_def]
    split_ifs <;> simp [Real.norm_eq_abs, sq_nonneg])

/-- An elementary truncated layer-cake estimate. -/
theorem TailB_square_error_truncation (C x y : ℝ) (hC : 0 ≤ C) :
    (x - y) ^ 2 ≤
      4 * (if C ^ 2 ≤ x ^ 2 then x ^ 2 else 0) +
      4 * (if C ^ 2 ≤ y ^ 2 then y ^ 2 else 0) +
      2 * C * (∫ t in (-C)..C,
        |(if x ≤ t then (1 : ℝ) else 0) - (if y ≤ t then 1 else 0)|) := by
  have hk : 0 ≤ (∫ t in (-C)..C,
      |(if x ≤ t then (1 : ℝ) else 0) - (if y ≤ t then 1 else 0)|) :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => abs_nonneg _)
  have hk' := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC) hk
  by_cases hx : C ^ 2 ≤ x ^ 2 <;> by_cases hy : C ^ 2 ≤ y ^ 2
  · simp only [if_pos hx, if_pos hy]
    nlinarith [sq_nonneg (x + y)]
  · simp only [if_pos hx, if_neg hy]
    nlinarith [sq_nonneg (x + y), lt_of_not_ge hy]
  · simp only [if_neg hx, if_pos hy]
    nlinarith [sq_nonneg (x + y), lt_of_not_ge hx]
  · simp only [if_neg hx, if_neg hy, mul_zero, zero_add]
    have hxc : x ∈ Icc (-C) C := by
      constructor <;> nlinarith [lt_of_not_ge hx]
    have hyc : y ∈ Icc (-C) C := by
      constructor <;> nlinarith [lt_of_not_ge hy]
    rw [← Causalean.Stat.Quantile.Transport.abs_sub_eq_integral_Icc_indicator hxc hyc]
    have hab : |x - y| ≤ 2 * C := abs_le.mpr ⟨by linarith [hxc.1, hyc.2],
      by linarith [hxc.2, hyc.1]⟩
    nlinarith [abs_nonneg (x-y), sq_abs (x-y)]

/-- L2 transport is controlled by square tails and a compact CDF integral.
This estimate is valid at atoms and does not use a uniform CDF metric. -/
theorem TailB_quantile_square_error_le
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (quantile μ) 2 unifOI) (hν : MemLp (quantile ν) 2 unifOI)
    (C : ℝ) (hC : 0 ≤ C) :
    (∫ u, (quantile μ u - quantile ν u) ^ 2 ∂unifOI) ≤
      4 * (∫ x, if C ^ 2 ≤ x ^ 2 then x ^ 2 else 0 ∂μ) +
      4 * (∫ x, if C ^ 2 ≤ x ^ 2 then x ^ 2 else 0 ∂ν) +
      2 * C * (∫ x in (-C)..C, |cdf μ x - cdf ν x|) := by
  let K : ℝ → ℝ := fun u => ∫ t in (-C)..C,
    |(if quantile μ u ≤ t then (1 : ℝ) else 0) -
      (if quantile ν u ≤ t then 1 else 0)|
  have hK : Integrable K unifOI := by
    have hh := (Causalean.Stat.Quantile.Transport.indicator_kernel_integrable
      μ ν (a := -C) (b := C)).integral_prod_left
    simpa only [K, intervalIntegral.integral_of_le (by linarith : -C ≤ C)] using hh
  have hKint : (∫ u, K u ∂unifOI) = ∫ x in (-C)..C, |cdf μ x - cdf ν x| := by
    rw [show (∫ u, K u ∂unifOI) = ∫ u in (0 : ℝ)..1, K u from
      TailB_integral_Ioo_eq_intervalIntegral K]
    exact Causalean.Stat.Quantile.Transport.indicator_integral_eq_cdf_distance μ ν
      (by linarith : -C ≤ C)
  have hTμ := TailB_square_tail_integrable hμ (C ^ 2)
  have hTν := TailB_square_tail_integrable hν (C ^ 2)
  calc
    _ ≤ ∫ u, 4 * (if C ^ 2 ≤ quantile μ u ^ 2 then quantile μ u ^ 2 else 0) +
        4 * (if C ^ 2 ≤ quantile ν u ^ 2 then quantile ν u ^ 2 else 0) +
        2 * C * K u ∂unifOI := by
      apply integral_mono_ae (hμ.sub hν).integrable_sq
        (((hTμ.const_mul 4).add (hTν.const_mul 4)).add (hK.const_mul (2*C)))
      exact ae_of_all _ (fun u => TailB_square_error_truncation C _ _ hC)
    _ = (4 * (∫ u, if C ^ 2 ≤ quantile μ u ^ 2 then quantile μ u ^ 2 else 0 ∂unifOI) +
        4 * (∫ u, if C ^ 2 ≤ quantile ν u ^ 2 then quantile ν u ^ 2 else 0 ∂unifOI)) +
        2 * C * (∫ u, K u ∂unifOI) := by
      calc
        _ = (∫ u, 4 * (if C ^ 2 ≤ quantile μ u ^ 2 then quantile μ u ^ 2 else 0) +
          4 * (if C ^ 2 ≤ quantile ν u ^ 2 then quantile ν u ^ 2 else 0) ∂unifOI) +
            ∫ u, 2 * C * K u ∂unifOI :=
          integral_add ((hTμ.const_mul 4).add (hTν.const_mul 4)) (hK.const_mul (2*C))
        _ = _ := by
          rw [integral_add (hTμ.const_mul 4) (hTν.const_mul 4)]
          simp only [integral_const_mul]
    _ = _ := by
      have hm : Measurable (fun x : ℝ => if C ^ 2 ≤ x ^ 2 then x ^ 2 else 0) :=
        Measurable.ite (measurableSet_le measurable_const (measurable_id.pow_const 2))
          (measurable_id.pow_const 2) measurable_const
      rw [hKint, TailB_integral_quantile μ _ hm, TailB_integral_quantile ν _ hm]

/-- Squared quantile error between two finite empirical laws. -/
def TailB_quantileSquareError {m k : ℕ} [NeZero m] [NeZero k]
    (a : Fin m → ℝ) (b : Fin k → ℝ) : ℝ :=
  ∫ u, (quantile (TailB_empiricalLaw a : Measure ℝ) u -
    quantile (TailB_empiricalLaw b : Measure ℝ) u) ^ 2 ∂unifOI

/-- This error is nonnegative. -/
theorem TailB_quantileSquareError_nonneg {m k : ℕ} [NeZero m] [NeZero k]
    (a : Fin m → ℝ) (b : Fin k → ℝ) : 0 ≤ TailB_quantileSquareError a b :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- A permutation block has the population mean in expectation. -/
theorem TailB_block_mean (d : Design) {s : ℕ} [NeZero s]
    (e : Fin s → Fin d.N) (z : Fin d.N → ℝ) :
    designExpectation d (fun π => finiteMean (fun i => z (π (e i)))) = finiteMean z := by
  unfold designExpectation finiteMean
  rw [Finset.expect_comm]
  simp_rw [permutation_eval_mean (show 0 < d.N by have := d.population_min; omega)]
  exact Fintype.expect_const _

/-- Finite permutation sampling preserves the expected square tail. -/
theorem TailB_sample_quantile_square_error_bound
    (d : Design) [NeZero d.N] {s : ℕ} [NeZero s]
    (e : Fin s → Fin d.N) (y : Fin d.N → ℝ) (C : ℝ) (hC : 0 ≤ C) :
    designExpectation d (fun π => TailB_quantileSquareError (fun i => y (π (e i))) y) ≤
      8 * finiteMean (fun i => if C ^ 2 ≤ y i ^ 2 then y i ^ 2 else 0) +
      2 * C * designExpectation d (fun π => integratedCDFError C y (fun i => y (π (e i)))) := by
  have hpoint (π : Assignment d) := TailB_quantile_square_error_le
    (TailB_empiricalLaw (fun i => y (π (e i))) : Measure ℝ)
    (TailB_empiricalLaw y : Measure ℝ)
    (TailB_empirical_quantile_memLp _) (TailB_empirical_quantile_memLp _) C hC
  have hm : Measurable (fun x : ℝ => if C ^ 2 ≤ x ^ 2 then x ^ 2 else 0) :=
    Measurable.ite (measurableSet_le measurable_const (measurable_id.pow_const 2))
      (measurable_id.pow_const 2) measurable_const
  simp only [TailB_integral_empiricalLaw _ _ hm, TailB_cdf_empiricalLaw] at hpoint
  calc
    _ ≤ designExpectation d (fun π =>
      4 * finiteMean (fun i => if C ^ 2 ≤ y (π (e i)) ^ 2 then y (π (e i)) ^ 2 else 0) +
      4 * finiteMean (fun i => if C ^ 2 ≤ y i ^ 2 then y i ^ 2 else 0) +
      2 * C * integratedCDFError C y (fun i => y (π (e i)))) := by
      exact Finset.expect_le_expect (fun π _ => hpoint π)
    _ = _ := by
      simp only [designExpectation, Finset.expect_add_distrib, ← Finset.mul_expect,
        Fintype.expect_const]
      rw [show (𝔼 π : Assignment d, finiteMean (fun i =>
        if C ^ 2 ≤ y (π (e i)) ^ 2 then y (π (e i)) ^ 2 else 0)) =
          finiteMean (fun i => if C ^ 2 ≤ y i ^ 2 then y i ^ 2 else 0) from
            TailB_block_mean d e (fun i => if C ^ 2 ≤ y i ^ 2 then y i ^ 2 else 0)]
      ring

/-- Cauchy--Schwarz for the actual finite randomization expectation. -/
theorem TailB_design_mean_sq_le (d : Design) (f : Assignment d → ℝ) :
    designExpectation d f ^ 2 ≤ designExpectation d (fun π => f π ^ 2) := by
  simpa only [designExpectation, mul_one, one_pow, Fintype.expect_const] using
    Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f (fun _ => (1 : ℝ))

/-- Integrated CDF error tends to zero in mean for growing injected blocks.
The assignment spaces and their uniform laws may change in every row. -/
theorem TailB_sample_integratedCDFError_tendsto
    (d : ℕ → Design) (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (e : (n : ℕ) → Fin (s n) → Fin (d n).N)
    (he : ∀ n, Function.Injective (e n)) (y : (n : ℕ) → Fin (d n).N → ℝ)
    (hsTop : Tendsto (fun n => (s n : ℝ)) atTop atTop) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun n => designExpectation (d n) (fun π =>
      integratedCDFError C (y n) (fun i => y n (π (e n i))))) atTop (𝓝 0) := by
  let D := fun n (π : Assignment (d n)) =>
    integratedCDFError C (y n) (fun i => y n (π (e n i)))
  have hD (n) (π : Assignment (d n)) : 0 ≤ D n π :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => abs_nonneg _)
  have hbound (n) : designExpectation (d n) (fun π => D n π ^ 2) ≤
      2 * C ^ 2 / s n := by
    have hm := GP022B1b_integrated_moment (d n) (hs n) (e n) (he n) (y n) C hC
    apply hm.trans
    have hN : (4 : ℝ) ≤ (d n).N := by exact_mod_cast (d n).population_min
    have hsR : (0 : ℝ) < s n := by exact_mod_cast hs n
    apply (div_le_div_iff₀ (mul_pos (by linarith : (0 : ℝ) < (d n).N - 1) hsR) hsR).mpr
    have hpos : 0 ≤ C ^ 2 * (s n : ℝ) := mul_nonneg (sq_nonneg _) hsR.le
    nlinarith
  have hsq : Tendsto (fun n => designExpectation (d n) (D n) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _)
      (fun n => (TailB_design_mean_sq_le (d n) (D n)).trans (hbound n))
    exact tendsto_const_nhds.div_atTop hsTop
  have hnn (n) : 0 ≤ designExpectation (d n) (D n) :=
    Finset.expect_nonneg (fun π _ => hD n π)
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (hnn _),
    Real.sqrt_zero] using hh

/-- First-moment Markov inequality for finite randomization laws. -/
theorem TailB_design_markov (d : Design) (f : Assignment d → ℝ)
    (hf : ∀ π, 0 ≤ f π) (ε : ℝ) (hε : 0 < ε) :
    designProbability d (fun π => ε ≤ f π) ≤ designExpectation d f / ε := by
  classical
  unfold designProbability designExpectation
  rw [Finset.expect_div]
  apply Finset.expect_le_expect
  intro π _
  split_ifs with h
  · exact (le_div_iff₀ hε).mpr (by simpa using h)
  · exact div_nonneg (hf π) hε.le

/-- Expected squared quantile error tends to zero under finite square-tail
control. No fixed probability space of assignments is assumed. -/
theorem TailB_sample_quantile_L2_mean
    (d : ℕ → Design) [∀ n, NeZero (d n).N]
    (s : ℕ → ℕ) [∀ n, NeZero (s n)]
    (e : (n : ℕ) → Fin (s n) → Fin (d n).N)
    (he : ∀ n, Function.Injective (e n)) (y : (n : ℕ) → Fin (d n).N → ℝ)
    (hsTop : Tendsto (fun n => (s n : ℝ)) atTop atTop)
    (htail : ∀ ε > 0, ∃ β : ℝ, 1 < β ∧ ∀ n,
      finiteMean (fun i => if β ≤ y n i ^ 2 then y n i ^ 2 else 0) ≤ ε) :
    Tendsto (fun n => designExpectation (d n) (fun π =>
      TailB_quantileSquareError (fun i => y n (π (e n i))) (y n))) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨C, hC, htailC⟩ := htail (ε / 16) (by positivity)
  have hC0 : 0 ≤ C := by linarith
  have hpop (n) : finiteMean (fun i => if C ^ 2 ≤ y n i ^ 2 then y n i ^ 2 else 0) ≤ ε / 16 := by
    apply le_trans _ (htailC n)
    apply Finset.expect_le_expect
    intro i _
    by_cases hy : C ^ 2 ≤ y n i ^ 2
    · have hh : C ≤ y n i ^ 2 := by nlinarith
      simp [hy, hh]
    · simp only [hy, if_false]
      split_ifs <;> positivity
  have hCDF := (TailB_sample_integratedCDFError_tendsto d s (fun n => NeZero.pos (s n))
    e he y hsTop C hC0).const_mul (2*C)
  have hsmall : ∀ᶠ n in atTop, 2 * C * designExpectation (d n) (fun π =>
      integratedCDFError C (y n) (fun i => y n (π (e n i)))) < ε / 2 := by
    exact hCDF.eventually_lt_const (by simpa using half_pos hε)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hsmall
  refine ⟨M, fun n hn => ?_⟩
  have hb := TailB_sample_quantile_square_error_bound (d n) (e n) (y n) C hC0
  have hnonneg : 0 ≤ designExpectation (d n) (fun π =>
      TailB_quantileSquareError (fun i => y n (π (e n i))) (y n)) :=
    Finset.expect_nonneg (fun π _ => TailB_quantileSquareError_nonneg _ _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith [hM n hn, hpop n]

/-- Squared L2 quantile error converges in probability for the actual
row-specific uniform permutation designs. -/
theorem TailB_sample_quantile_L2_probability
    (d : ℕ → Design) [∀ n, NeZero (d n).N]
    (s : ℕ → ℕ) [∀ n, NeZero (s n)]
    (e : (n : ℕ) → Fin (s n) → Fin (d n).N)
    (he : ∀ n, Function.Injective (e n)) (y : (n : ℕ) → Fin (d n).N → ℝ)
    (hsTop : Tendsto (fun n => (s n : ℝ)) atTop atTop)
    (htail : ∀ ε > 0, ∃ β : ℝ, 1 < β ∧ ∀ n,
      finiteMean (fun i => if β ≤ y n i ^ 2 then y n i ^ 2 else 0) ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => designProbability (d n) (fun π =>
      ε ≤ TailB_quantileSquareError (fun i => y n (π (e n i))) (y n))) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => Finset.expect_nonneg (fun _ _ => by split_ifs <;> norm_num))
    (fun n => TailB_design_markov (d n) _ (fun _ => TailB_quantileSquareError_nonneg _ _) ε hε)
  simpa using (TailB_sample_quantile_L2_mean d s e he y hsTop htail).div_const ε

/-- L2 convergence as convergence in the actual Hilbert space. -/
theorem TailB_toLp_tendsto {α : Type*} [MeasurableSpace α] {m : Measure α}
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ n, MemLp (f n) 2 m) (hg : MemLp g 2 m)
    (ht : Tendsto (fun n => eLpNorm (f n - g) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp_rw [Lp.dist_edist, Lp.edist_toLp_toLp]
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp ht

/-- The Hilbert-space pairing is the literal real product integral. -/
theorem TailB_toLp_inner {α : Type*} [MeasurableSpace α] {m : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂m := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]

/-- Two L2-convergent sequences have convergent product integrals. -/
theorem TailB_L2_product_tendsto {α : Type*} [MeasurableSpace α] {m : Measure α}
    (f g : ℕ → α → ℝ) (f₀ g₀ : α → ℝ)
    (hf : ∀ n, MemLp (f n) 2 m) (hg : ∀ n, MemLp (g n) 2 m)
    (hf₀ : MemLp f₀ 2 m) (hg₀ : MemLp g₀ 2 m)
    (htf : Tendsto (fun n => eLpNorm (f n - f₀) 2 m) atTop (𝓝 0))
    (htg : Tendsto (fun n => eLpNorm (g n - g₀) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x * g n x ∂m) atTop (𝓝 (∫ x, f₀ x * g₀ x ∂m)) := by
  have hh := (TailB_toLp_tendsto f f₀ hf hf₀ htf).inner
    (𝕜 := ℝ) (TailB_toLp_tendsto g g₀ hg hg₀ htg)
  simpa only [TailB_toLp_inner] using hh

/-- Both first and second moments are continuous for L2 convergence. -/
theorem TailB_L2_moments_tendsto {α : Type*} [MeasurableSpace α]
    {m : Measure α} [IsFiniteMeasure m]
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ n, MemLp (f n) 2 m) (hg : MemLp g 2 m)
    (ht : Tendsto (fun n => eLpNorm (f n - g) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂m) atTop (𝓝 (∫ x, g x ∂m)) ∧
    Tendsto (fun n => ∫ x, f n x ^ 2 ∂m) atTop (𝓝 (∫ x, g x ^ 2 ∂m)) := by
  constructor
  · have hh := TailB_L2_product_tendsto f (fun _ _ => (1 : ℝ)) g (fun _ => (1 : ℝ))
      hf (fun _ => memLp_const 1) hg (memLp_const 1) ht (by simpa using tendsto_const_nhds)
    simpa only [mul_one] using hh
  · simpa only [pow_two] using TailB_L2_product_tendsto f f g g hf hf hg hg ht ht

/-- Reflection of the uniform level preserves the L2 seminorm. -/
theorem TailB_reflected_eLpNorm (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f unifOI) :
    eLpNorm (fun u => f (1-u)) 2 unifOI = eLpNorm f 2 unifOI := by
  have hm : Measurable (fun u : ℝ => 1-u) := measurable_const.sub measurable_id
  have hh : AEStronglyMeasurable f (unifOI.map (fun u : ℝ => 1-u)) := by
    rwa [map_one_sub_unifOI]
  simpa only [map_one_sub_unifOI, Function.comp_def] using
    (eLpNorm_map_measure hh hm.aemeasurable).symm

/-- Reflection preserves the L2 class. -/
theorem TailB_reflected_memLp {f : ℝ → ℝ} (hf : MemLp f 2 unifOI) :
    MemLp (fun u => f (1-u)) 2 unifOI := by
  simpa only [MemLp, TailB_reflected_eLpNorm f hf.aestronglyMeasurable] using hf

/-- The actual L2 distance between finite quantiles has the square-error form. -/
theorem TailB_toLp_dist_sq {m k : ℕ} [NeZero m] [NeZero k]
    (a : Fin m → ℝ) (b : Fin k → ℝ) :
    dist ((TailB_empirical_quantile_memLp a).toLp
      (quantile (TailB_empiricalLaw a : Measure ℝ)))
      ((TailB_empirical_quantile_memLp b).toLp
      (quantile (TailB_empiricalLaw b : Measure ℝ))) ^ 2 = TailB_quantileSquareError a b := by
  rw [Lp.dist_edist, Lp.edist_toLp_toLp, ← ENNReal.toReal_pow,
    TailB_eLpNorm_two_sq ((TailB_empirical_quantile_memLp a).sub
      (TailB_empirical_quantile_memLp b))]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _))

/-- Convergence in probability under the separate finite design in every row. -/
def TailB_DesignTendsto {E : Type*} [PseudoMetricSpace E]
    (d : ℕ → Design) (X : (n : ℕ) → Assignment (d n) → E) (x : E) : Prop :=
  ∀ ε > 0, Tendsto (fun n => designProbability (d n) (fun π => ε ≤ dist (X n π) x))
    atTop (𝓝 0)

/-- Finite event monotonicity, without a common assignment space. -/
theorem TailB_designProbability_mono (d : Design) (E F : Assignment d → Prop)
    (hEF : ∀ π, E π → F π) : designProbability d E ≤ designProbability d F := by
  classical
  apply Finset.expect_le_expect
  intro π _
  by_cases h : E π
  · simp only [if_pos h, if_pos (hEF π h), le_refl]
  · simp only [if_neg h]
    split_ifs <;> norm_num

/-- The probability of a union is at most the sum of the two probabilities. -/
theorem TailB_designProbability_union (d : Design) (E F : Assignment d → Prop) :
    designProbability d (fun π => E π ∨ F π) ≤
      designProbability d E + designProbability d F := by
  classical
  unfold designProbability designExpectation
  rw [← Finset.expect_add_distrib]
  apply Finset.expect_le_expect
  intro π _
  by_cases he : E π <;> by_cases hf : F π <;> simp [he, hf]

/-- A deterministic convergent row is convergent in design probability. -/
theorem TailB_DesignTendsto.deterministic {E : Type*} [PseudoMetricSpace E]
    (d : ℕ → Design) {x : ℕ → E} {a : E} (hx : Tendsto x atTop (𝓝 a)) :
    TailB_DesignTendsto d (fun n _ => x n) a := by
  intro ε hε
  have he := (tendsto_iff_dist_tendsto_zero.mp hx).eventually_lt_const hε
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  simp [designProbability, designExpectation, not_le.mpr hn]

/-- The continuous mapping theorem uses only event inclusion. -/
theorem TailB_DesignTendsto.comp {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {d : ℕ → Design} {X : (n : ℕ) → Assignment (d n) → E} {a : E}
    (hX : TailB_DesignTendsto d X a) (f : E → F) (hf : ContinuousAt f a) :
    TailB_DesignTendsto d (fun n π => f (X n π)) (f a) := by
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hf ε hε
  apply squeeze_zero (fun _ => Finset.expect_nonneg (fun _ _ => by split_ifs <;> norm_num))
    (fun n => TailB_designProbability_mono (d n) _ _ (fun π hp => ?_)) (hX δ hδ)
  by_contra hh
  have hlt := hd (lt_of_not_ge hh)
  exact (not_lt.mpr hp) hlt

/-- Joint convergence needs no independence under finite randomization. -/
theorem TailB_DesignTendsto.prod {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {d : ℕ → Design} {X : (n : ℕ) → Assignment (d n) → E}
    {Y : (n : ℕ) → Assignment (d n) → F} {a : E} {b : F}
    (hX : TailB_DesignTendsto d X a) (hY : TailB_DesignTendsto d Y b) :
    TailB_DesignTendsto d (fun n π => (X n π, Y n π)) (a,b) := by
  intro ε hε
  apply squeeze_zero (fun _ => Finset.expect_nonneg (fun _ _ => by split_ifs <;> norm_num))
    (fun n => ?_) (by simpa only [zero_add] using (hX ε hε).add (hY ε hε))
  calc
    _ ≤ designProbability (d n) (fun π =>
        ε ≤ dist (X n π) a ∨ ε ≤ dist (Y n π) b) :=
      TailB_designProbability_mono (d n) _ _ (fun π hp => by
        simpa only [Prod.dist_eq, le_max_iff] using hp)
    _ ≤ _ := TailB_designProbability_union (d n) _ _

/-- A perturbation of a convergent deterministic row has the same limit. -/
theorem TailB_DesignTendsto.of_perturbation {E : Type*} [PseudoMetricSpace E]
    {d : ℕ → Design} (X : (n : ℕ) → Assignment (d n) → E) (a : ℕ → E) (b : E)
    (ha : Tendsto a atTop (𝓝 b))
    (hXa : ∀ ε > 0, Tendsto (fun n => designProbability (d n)
      (fun π => ε ≤ dist (X n π) (a n))) atTop (𝓝 0)) :
    TailB_DesignTendsto d X b := by
  intro ε hε
  have he : ∀ᶠ n in atTop, dist (a n) b < ε / 2 :=
    (tendsto_iff_dist_tendsto_zero.mp ha).eventually_lt_const (half_pos hε)
  apply squeeze_zero' (Eventually.of_forall (fun _ =>
    Finset.expect_nonneg (fun _ _ => by split_ifs <;> norm_num))) ?_ (hXa (ε/2) (half_pos hε))
  filter_upwards [he] with n hn
  apply TailB_designProbability_mono (d n) _ _
  intro π hp
  have hh := dist_triangle (X n π) (a n) b
  linarith

/-- Finite sampled quantiles converge to the limiting quantile as elements of
one fixed L2 Hilbert space. -/
theorem TailB_sample_quantile_toLp
    (d : ℕ → Design) [∀ n, NeZero (d n).N]
    (s : ℕ → ℕ) [∀ n, NeZero (s n)]
    (e : (n : ℕ) → Fin (s n) → Fin (d n).N)
    (he : ∀ n, Function.Injective (e n)) (y : (n : ℕ) → Fin (d n).N → ℝ)
    (hsTop : Tendsto (fun n => (s n : ℝ)) atTop atTop)
    (htail : ∀ ε > 0, ∃ β : ℝ, 1 < β ∧ ∀ n,
      finiteMean (fun i => if β ≤ y n i ^ 2 then y n i ^ 2 else 0) ≤ ε)
    (g : ℝ → ℝ) (hg : MemLp g 2 unifOI)
    (hpop : Tendsto (fun n => eLpNorm
      (quantile (TailB_empiricalLaw (y n) : Measure ℝ) - g) 2 unifOI) atTop (𝓝 0)) :
    TailB_DesignTendsto d (fun n π =>
      (TailB_empirical_quantile_memLp (fun i => y n (π (e n i)))).toLp
        (quantile (TailB_empiricalLaw (fun i => y n (π (e n i))) : Measure ℝ)))
      (hg.toLp g) := by
  apply TailB_DesignTendsto.of_perturbation _
    (fun n => (TailB_empirical_quantile_memLp (y n)).toLp
      (quantile (TailB_empiricalLaw (y n) : Measure ℝ))) _
    (TailB_toLp_tendsto _ g (fun n => TailB_empirical_quantile_memLp (y n)) hg hpop)
  intro ε hε
  apply squeeze_zero (fun _ => Finset.expect_nonneg (fun _ _ => by split_ifs <;> norm_num))
    (fun n => TailB_designProbability_mono (d n) _ _ (fun π hp => ?_))
    (TailB_sample_quantile_L2_probability d s e he y hsTop htail (ε^2) (sq_pos_of_pos hε))
  rw [← TailB_toLp_dist_sq]
  exact pow_le_pow_left₀ hε.le hp 2

/-- Addition under the varying finite randomization laws. -/
theorem TailB_DesignTendsto.add {d : ℕ → Design}
    {X Y : (n : ℕ) → Assignment (d n) → ℝ} {a b : ℝ}
    (hX : TailB_DesignTendsto d X a) (hY : TailB_DesignTendsto d Y b) :
    TailB_DesignTendsto d (fun n π => X n π + Y n π) (a+b) :=
  (hX.prod hY).comp (fun p => p.1+p.2) (by fun_prop)

/-- Subtraction under the varying finite randomization laws. -/
theorem TailB_DesignTendsto.sub {d : ℕ → Design}
    {X Y : (n : ℕ) → Assignment (d n) → ℝ} {a b : ℝ}
    (hX : TailB_DesignTendsto d X a) (hY : TailB_DesignTendsto d Y b) :
    TailB_DesignTendsto d (fun n π => X n π - Y n π) (a-b) :=
  (hX.prod hY).comp (fun p => p.1-p.2) (by fun_prop)

/-- Multiplication under the varying finite randomization laws. -/
theorem TailB_DesignTendsto.mul {d : ℕ → Design}
    {X Y : (n : ℕ) → Assignment (d n) → ℝ} {a b : ℝ}
    (hX : TailB_DesignTendsto d X a) (hY : TailB_DesignTendsto d Y b) :
    TailB_DesignTendsto d (fun n π => X n π * Y n π) (a*b) :=
  (hX.prod hY).comp (fun p => p.1*p.2) (by fun_prop)
