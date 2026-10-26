import AronowAudit.P001.Wave1.Lib.TailA.OuterReadout
import Mathlib.Topology.Sequences

/-! A scalar Hadamard delta theorem for arbitrary outer-convergent paths. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace AronowAudit.P001.Wave1.TailA

set_option maxHeartbeats 800000

/-- The indicator-majorant outer mass is the measure's value even on an
arbitrary set. This allows outer portmanteau to control `CP`. -/
theorem delta_outer_mass_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) : μ.outerMeasureStar A = μ A := by
  classical
  apply le_antisymm (AsymptoticStatistics.outerMeasureStar_le_measure μ A)
  change μ A ≤ outerExpectation μ (A.indicator 1)
  apply le_iInf
  intro U
  let B : Set Ω := {ω | 1 ≤ U.val ω}
  have hB : MeasurableSet B := measurableSet_le measurable_const U.property.1
  calc
    μ A ≤ μ B := measure_mono (by
      intro ω hω
      exact (show (A.indicator (1 : Ω → ℝ≥0∞)) ω ≤ U.val ω from
        U.property.2 ω).trans' (by simp [hω]))
    _ = ∫⁻ ω, B.indicator (1 : Ω → ℝ≥0∞) ω ∂μ :=
      (lintegral_indicator_one hB).symm
    _ ≤ ∫⁻ ω, U.val ω ∂μ := lintegral_mono (by
      intro ω
      by_cases hω : ω ∈ B
      · simpa only [Set.indicator_of_mem hω, Pi.one_apply] using
          (show 1 ≤ U.val ω from hω)
      · simp only [Set.indicator_of_notMem hω]
        exact bot_le)

/-- Sequential Hadamard differentiability is uniform for domain-valid
directions near a compact subset of the tangent set. -/
theorem delta_hadamard_uniform_compact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D H : Set E) (θ : E) (T : E → ℝ) (L : E →L[ℝ] ℝ)
    (hd : HadamardAt D H T θ L) (K : Set E) (hK : IsCompact K)
    (hKH : K ⊆ H) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ v : E,
      v ∈ Metric.thickening δ K → θ + t • v ∈ D →
      |(T (θ + t • v) - T θ) / t - L v| < ε := by
  classical
  by_contra hbad
  push Not at hbad
  let a : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hex (n : ℕ) := hbad (a n) (ha n)
  choose t ht ht_small v hv hvD hvbad using hex
  have ht0 : Tendsto t atTop (𝓝 0) :=
    squeeze_zero (fun n => (ht n).le) (fun n => (ht_small n).le) ha0
  have hnear (n : ℕ) : ∃ k ∈ K, dist (v n) k < a n :=
    Metric.mem_thickening_iff.mp (hv n)
  choose k hk hdist using hnear
  obtain ⟨z, hz, φ, hφ, hk0⟩ := hK.tendsto_subseq hk
  have hd0 : Tendsto (fun n => dist (k (φ n)) (v (φ n))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => (by simpa only [dist_comm] using (hdist (φ n)).le))
    exact ha0.comp hφ.tendsto_atTop
  have hv0 : Tendsto (fun n => v (φ n)) atTop (𝓝 z) := hk0.congr_dist hd0
  have hquot := hd z (hKH hz) (fun n => t (φ n)) (fun n => v (φ n))
    (fun n => ht (φ n)) (ht0.comp hφ.tendsto_atTop) hv0 (fun n => hvD (φ n))
  have hrem : Tendsto (fun n =>
      |(T (θ + t (φ n) • v (φ n)) - T θ) / t (φ n) - L (v (φ n))|)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self, abs_zero] using
      (hquot.sub (L.continuous.tendsto z |>.comp hv0)).abs
  have hsmall := hrem.eventually_lt_const hε
  obtain ⟨n, hn⟩ := hsmall.exists
  exact (not_lt_of_ge (hvbad (φ n))) hn

/-- A tight law supported by a closed tangent set has compact subsets of that
set carrying arbitrarily large probability. -/
theorem delta_tight_compact_tangent {E : Type*} [MetricSpace E]
    [MeasurableSpace E] (ν : Measure E) (H : Set E) (hH : IsClosed H)
    (hνH : ν Hᶜ = 0) (htight : IsTightMeasureSet ({ν} : Set (Measure E)))
    (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ H ∧ ν Kᶜ ≤ η := by
  obtain ⟨K, hK, hmass⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight η hη
  refine ⟨K ∩ H, hK.inter_right hH, Set.inter_subset_right, ?_⟩
  calc
    ν (K ∩ H)ᶜ = ν (Kᶜ ∪ Hᶜ) := by rw [Set.compl_inter]
    _ ≤ ν Kᶜ + ν Hᶜ := measure_union_le _ _
    _ ≤ η := by simpa only [hνH, add_zero] using hmass ν rfl

/-- The actual Hadamard remainder tends to zero in outer probability.
Neither the paths nor their linear images need be measurable. -/
theorem delta_hadamard_remainder_CP {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D H : Set E) (θ : E)
    (hH : IsClosed H) (T : E → ℝ) (L : E →L[ℝ] ℝ)
    (hd : HadamardAt D H T θ L) (Z : ℕ → Ω → E)
    (hD : ∀ᶠ n in atTop, ∀ ω, Z n ω ∈ D)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (ν : Measure E) [IsProbabilityMeasure ν] (hνH : ν Hᶜ = 0)
    (htight : IsTightMeasureSet ({ν} : Set (Measure E)))
    (hw : OuterWeakLimit μ (fun n ω => r n • (Z n ω - θ)) ν) :
    CP μ (fun n ω => r n * (T (Z n ω) - T θ) -
      L (r n • (Z n ω - θ))) 0 := by
  let X : ℕ → Ω → E := fun n ω => r n • (Z n ω - θ)
  let R : ℕ → Ω → ℝ := fun n ω => r n * (T (Z n ω) - T θ) - L (X n ω)
  have hw' : AsymptoticStatistics.WeakConvergesOuter (fun _ => μ) X ν :=
    (outer_weak_donor_iff μ X ν).mp hw
  have hrpos : ∀ᶠ n in atTop, 0 < r n := hr.eventually_gt_atTop 0
  have ht0 : Tendsto (fun n => (r n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hr
  change CP μ R 0
  intro ε hε
  have hzero : limsup (fun n => μ {ω | ε ≤ dist (R n ω) 0}) atTop ≤ 0 := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro η hη
    obtain ⟨K, hK, hKH, hmass⟩ :=
      delta_tight_compact_tangent ν H hH hνH htight η hη
    obtain ⟨δ, hδ, huniform⟩ :=
      delta_hadamard_uniform_compact D H θ T L hd K hK hKH ε hε
    have htsmall : ∀ᶠ n in atTop, (r n)⁻¹ < δ := ht0.eventually_lt_const hδ
    have hbound : ∀ᶠ n in atTop,
        μ {ω | ε ≤ dist (R n ω) 0} ≤
          μ.outerMeasureStar (X n ⁻¹' (Metric.thickening δ K)ᶜ) := by
      filter_upwards [hrpos, htsmall, hD] with n hn hnt hnD
      rw [delta_outer_mass_eq]
      apply measure_mono
      intro ω hω
      change X n ω ∉ Metric.thickening δ K
      intro hnear
      have hrecover : θ + (r n)⁻¹ • X n ω = Z n ω := by
        dsimp only [X]
        rw [smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
        abel
      have hrem := huniform (r n)⁻¹ (inv_pos.mpr hn) hnt (X n ω) hnear
        (by simpa only [hrecover] using hnD ω)
      have heq : (T (θ + (r n)⁻¹ • X n ω) - T θ) / (r n)⁻¹ - L (X n ω) =
          R n ω := by
        rw [hrecover, div_inv_eq_mul]
        dsimp only [R]
        ring
      have hsmall : dist (R n ω) 0 < ε := by
        simpa only [heq, Real.dist_eq, sub_zero] using hrem
      exact (not_lt_of_ge hω) hsmall
    calc
      limsup (fun n => μ {ω | ε ≤ dist (R n ω) 0}) atTop
          ≤ limsup (fun n =>
            μ.outerMeasureStar (X n ⁻¹' (Metric.thickening δ K)ᶜ)) atTop :=
        limsup_le_limsup hbound
      _ ≤ ν (Metric.thickening δ K)ᶜ :=
        AsymptoticStatistics.limsup_outerMeasureStar_preimage_isClosed_le hw'
          Metric.isOpen_thickening.isClosed_compl
      _ ≤ ν Kᶜ := measure_mono (Set.compl_subset_compl.mpr
        (Metric.self_subset_thickening hδ K))
      _ ≤ η := hmass
  have ht : Tendsto (fun n => μ {ω | ε ≤ dist (R n ω) 0}) atTop (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le bot_le hzero
  simpa only [Function.comp_def, prob, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht

set_option linter.unusedVariables false in
/-- Scalar outer Hadamard delta method, with its actual probability remainder. -/
theorem outer_hadamard_delta_real {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D H : Set E) (θ : E)
    (hθ : θ ∈ D) (hH : IsClosed H) (hsH : TopologicalSpace.IsSeparable H)
    (T : E → ℝ) (L : E →L[ℝ] ℝ) (hd : HadamardAt D H T θ L)
    (Z : ℕ → Ω → E) (hD : ∀ᶠ n in atTop, ∀ ω, Z n ω ∈ D)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hνH : ν Hᶜ = 0) (htight : IsTightMeasureSet ({ν} : Set (Measure E)))
    (hw : OuterWeakLimit μ (fun n ω => r n • (Z n ω - θ)) ν)
    (hstat : ∀ n, Measurable (fun ω => T (Z n ω))) :
    CP μ (fun n ω => r n * (T (Z n ω) - T θ) - L (r n • (Z n ω - θ))) 0 ∧
    CD μ (fun n ω => r n * (T (Z n ω) - T θ)) (ν.map L) := by
  have hCP := delta_hadamard_remainder_CP μ D H θ hH T L hd Z hD r hr ν hνH htight hw
  refine ⟨hCP, ?_⟩
  let X : ℕ → Ω → ℝ := fun n ω => L (r n • (Z n ω - θ))
  let Y : ℕ → Ω → ℝ := fun n ω => r n * (T (Z n ω) - T θ)
  have hw' := (outer_weak_donor_iff μ (fun n ω => r n • (Z n ω - θ)) ν).mp hw
  have hL : AsymptoticStatistics.WeakConvergesOuter (fun _ => μ) X (ν.map L) :=
    hw'.continuous_comp L.continuous
  have hdist : ∀ δ > 0, Tendsto
      (fun n => μ.real {ω | δ ≤ dist (X n ω) (Y n ω)}) atTop (𝓝 0) := by
    intro δ hδ
    have heq (n : ℕ) : {ω | δ ≤ dist (X n ω) (Y n ω)} =
        {ω | δ ≤ dist (Y n ω - X n ω) 0} := by
      ext ω
      simp only [Real.dist_eq, sub_zero, abs_sub_comm]
    simpa only [heq, Measure.real, prob, X, Y] using hCP δ hδ
  have hY := hL.slutsky_of_tendstoInOuterProbability_dist hdist
  exact outer_weak_real_CD μ Y (ν.map L) ((outer_weak_donor_iff μ Y (ν.map L)).mpr hY)

end AronowAudit.P001.Wave1.TailA
