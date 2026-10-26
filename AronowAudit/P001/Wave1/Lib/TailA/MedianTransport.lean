import AronowAudit.P001.Wave1.Lib.TailA.BernoulliRows
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Convergence of conditional real CDFs transports to bounded continuous tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction

namespace AronowAudit.P001.TailA

universe u
local instance instDecidableMedianTransport (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Rational half-lines determine weak convergence of probability measures. -/
theorem medianTransport_weak_of_rational_cdf (Q : ℕ → ProbabilityMeasure ℝ)
    (G : ProbabilityMeasure ℝ)
    (h : ∀ q : ℚ, Tendsto (fun n => (Q n : Measure ℝ).real (Set.Iic (q : ℝ)))
      atTop (𝓝 ((G : Measure ℝ).real (Set.Iic (q : ℝ))))) :
    Tendsto Q atTop (𝓝 G) := by
  apply (isPiSystem_Ioc (fun q : ℚ => (q : ℝ)) (fun q : ℚ => (q : ℝ))).tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨a, b, hab, rfl⟩
    exact measurableSet_Ioc
  · intro U hU x hx
    obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
    obtain ⟨r, har, hrx⟩ := exists_rat_btwn hab.1
    obtain ⟨s, hxs, hsb⟩ := exists_rat_btwn hab.2
    refine ⟨Set.Ioc (r : ℝ) (s : ℝ), ⟨r, s, hrx.trans hxs, rfl⟩,
      Ioc_mem_nhds_iff.mpr ⟨hrx, hxs⟩, ?_⟩
    exact (fun y hy => hsub ⟨har.trans hy.1, hy.2.trans_lt hsb⟩)
  · rintro s ⟨a, b, hab, rfl⟩
    apply NNReal.tendsto_coe.mp
    simp only [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
    have he (P : ProbabilityMeasure ℝ) :
        (P : Measure ℝ).real (Set.Ioc (a : ℝ) (b : ℝ)) =
          (P : Measure ℝ).real (Set.Iic (b : ℝ)) - (P : Measure ℝ).real (Set.Iic (a : ℝ)) := by
      rw [← Set.Iic_sdiff_Iic, measureReal_sdiff (Set.Iic_subset_Iic.mpr hab.le) measurableSet_Iic]
    simp only [he]
    exact (h b).sub (h a)

/-- A fixed bounded continuous test is controlled by finitely many rational CDF coordinates.
This finite determination lemma is also useful when the candidate laws are random. -/
theorem medianTransport_finite_test (G : ProbabilityMeasure ℝ)
    (f : ℝ →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℚ, ∃ δ : ℝ, 0 < δ ∧ ∀ Q : ProbabilityMeasure ℝ,
      (∀ q ∈ s, |(Q : Measure ℝ).real (Set.Iic (q : ℝ)) -
        (G : Measure ℝ).real (Set.Iic (q : ℝ))| < δ) →
      |(∫ x, f x ∂(Q : Measure ℝ)) - ∫ x, f x ∂(G : Measure ℝ)| < ε := by
  obtain ⟨q, hq⟩ := exists_surjective_nat ℚ
  by_contra hno
  push_neg at hno
  have hex : ∀ n : ℕ, ∃ Q : ProbabilityMeasure ℝ,
      (∀ k ≤ n, |(Q : Measure ℝ).real (Set.Iic (q k : ℝ)) -
        (G : Measure ℝ).real (Set.Iic (q k : ℝ))| < 1 / ((n : ℝ) + 1)) ∧
      ε ≤ |(∫ x, f x ∂(Q : Measure ℝ)) - ∫ x, f x ∂(G : Measure ℝ)| := by
    intro n
    obtain ⟨Q, hQ, hbad⟩ := hno ((Finset.range (n+1)).image q)
      (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨Q, fun k hk => hQ (q k) (Finset.mem_image.mpr
      ⟨k, Finset.mem_range.mpr (by omega), rfl⟩), hbad⟩
  choose Q hQ hbad using hex
  have hlim : Tendsto Q atTop (𝓝 G) := by
    apply medianTransport_weak_of_rational_cdf
    intro r
    obtain ⟨k, rfl⟩ := hq r
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
      (show ∀ᶠ n in atTop, dist ((Q n : Measure ℝ).real (Set.Iic (q k : ℝ)))
        ((G : Measure ℝ).real (Set.Iic (q k : ℝ))) ≤ 1 / ((n : ℝ) + 1) from by
        filter_upwards [eventually_ge_atTop k] with n hn
        exact (hQ n k hn).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f
  have he : ∀ᶠ n in atTop, |(∫ x, f x ∂(Q n : Measure ℝ)) -
      ∫ x, f x ∂(G : Measure ℝ)| < ε := by
    simpa only [Real.dist_eq] using hf.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨n, hn⟩ := he.exists
  exact (not_lt_of_ge (hbad n)) hn

/-- Convergence in probability of the conditional rational CDFs suffices for every
bounded continuous test. No moment of the conditional laws is needed. -/
theorem medianTransport_test_cp {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Q : ℕ → Ω → ProbabilityMeasure ℝ)
    (G : ProbabilityMeasure ℝ)
    (hCDF : ∀ q : ℚ, CP μ (fun n ω => (Q n ω : Measure ℝ).real (Set.Iic (q : ℝ)))
      ((G : Measure ℝ).real (Set.Iic (q : ℝ)))) (f : ℝ →ᵇ ℝ) :
    CP μ (fun n ω => ∫ x, f x ∂(Q n ω : Measure ℝ)) (∫ x, f x ∂(G : Measure ℝ)) := by
  intro ε hε
  obtain ⟨s, δ, hδ, htest⟩ := medianTransport_finite_test G f ε hε
  have hbound (n : ℕ) :
      prob μ {ω | ε ≤ dist (∫ x, f x ∂(Q n ω : Measure ℝ)) (∫ x, f x ∂(G : Measure ℝ))} ≤
        ∑ q ∈ s, prob μ {ω | δ ≤ dist ((Q n ω : Measure ℝ).real (Set.Iic (q : ℝ)))
          ((G : Measure ℝ).real (Set.Iic (q : ℝ)))} := by
    apply le_trans (measureReal_mono (s₂ := ⋃ q ∈ s,
      {ω | δ ≤ dist ((Q n ω : Measure ℝ).real (Set.Iic (q : ℝ)))
        ((G : Measure ℝ).real (Set.Iic (q : ℝ)))}) ?_ (measure_ne_top μ _))
    · exact measureReal_biUnion_finset_le s _
    · intro ω hω
      by_contra hn
      have hsmall : ∀ q ∈ s, |(Q n ω : Measure ℝ).real (Set.Iic (q : ℝ)) -
          (G : Measure ℝ).real (Set.Iic (q : ℝ))| < δ := by
        intro q hq
        apply lt_of_not_ge
        intro h
        apply hn
        exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, h⟩⟩
      exact (not_lt_of_ge hω) (htest (Q n ω) hsmall)
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hbound
  simpa using tendsto_finsetSum s (fun q _ => hCDF q δ hδ)

/-- The finite conditional bootstrap laws have the required bounded-test interpretation. -/
theorem medianTransport_bootstrap_of_cdf {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (T : {n : ℕ} → (Fin n → ℝ) → ℝ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hCDF : ∀ z : ℝ, CP μ (fun n ω =>
      (CenteredBootstrapLaw T (firstSample X n ω)).real (Set.Iic z)) (G.real (Set.Iic z))) :
    BootstrapWeakCP μ X (fun n => n) T G := by
  intro f hf ⟨C, hC⟩
  let g : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2*C)
    (fun x y => by
      change |f x - f y| ≤ 2*C
      have hxy := abs_sub_le (f x) 0 (f y)
      simp only [sub_zero, zero_sub, abs_neg] at hxy
      linarith [hC x, hC y])
  have h := medianTransport_test_cp μ
    (fun n ω => ⟨CenteredBootstrapLaw T (firstSample X n ω), inferInstance⟩)
    ⟨G, inferInstance⟩ (fun q => hCDF q) g
  change CP μ (fun n ω => mean (CenteredBootstrapLaw T (firstSample X n ω)) f) (mean G f) at h
  simpa only [centered_bootstrap_test _ _ hf.measurable] using h

end AronowAudit.P001.TailA
