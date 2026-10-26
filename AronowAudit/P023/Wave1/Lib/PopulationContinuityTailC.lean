import AronowAudit.P023.Wave1.Lib.ContinuousBadMeanTailC
import AronowAudit.P023.Wave1.Lib.LipschitzBiasTailC
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Shrinking-window continuity and consequences for the single fixed bad mean. -/
namespace AronowAudit.P023.Wave1
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- On uniform margins the two window averages are ordinary interval averages. -/
theorem tc11_uniform_rd_formula (m : ℝ → ℝ) (k : ℝ) (hk : 0 < k) (hk1 : k ≤ 1) :
    populationRD uniformMargins m k =
      (∫ x in (0 : ℝ)..k, m x)/k - (∫ x in (0 : ℝ)..k, m (-x))/k := by
  have hpos : Ioc (0 : ℝ) k ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hneg : Ioo (-k) (0 : ℝ) ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hp : (∫ x in Ioc (0 : ℝ) k, m x ∂uniformMargins) =
      (1/2 : ℝ)*(∫ x in (0 : ℝ)..k, m x) := by
    rw [uniformMargins, Measure.restrict_smul, integral_smul_measure,
      Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr hpos,
      ← intervalIntegral.integral_of_le hk.le]
    norm_num
  have hn : (∫ x in Ioo (-k) (0 : ℝ), m x ∂uniformMargins) =
      (1/2 : ℝ)*(∫ x in (0 : ℝ)..k, m (-x)) := by
    rw [uniformMargins, Measure.restrict_smul, integral_smul_measure,
      Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hneg,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith : -k ≤ 0)]
    norm_num
  unfold populationRD
  rw [(GP023B1b_uniform_window k hk hk1).1, (GP023B1b_uniform_window k hk hk1).2, hp, hn]
  field_simp

theorem tc11_interval_average_zero (m : ℝ → ℝ) (hc : Continuous m) :
    Tendsto (fun k => (∫ x in (0 : ℝ)..k, m x)/k)
      (nhdsWithin 0 (Ioi 0)) (nhds (m 0)) := by
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (0 : ℝ) 0)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa only [zero_add, intervalIntegral.integral_same, sub_zero, smul_eq_mul, div_eq_mul_inv,
    mul_comm] using hd.tendsto_slope_zero_right

/-- Continuity at the cutoff makes the uniform shrinking-window difference tend to zero. -/
theorem populationRD_continuous_limit (m : ℝ → ℝ) (hc : Continuous m) :
    Tendsto (populationRD uniformMargins m) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have h := (tc11_interval_average_zero m hc).sub
    (tc11_interval_average_zero (fun x => m (-x)) (hc.comp continuous_neg))
  simp only [neg_zero, sub_self] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ k : ℝ in nhdsWithin 0 (Ioi 0), k < 1 from
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds)] with k hk hk1
  exact (tc11_uniform_rd_formula m k hk hk1.le).symm

/-- Any fixed function with the prescribed growing bias subsequence fails the exact Lipschitz clause. -/
theorem tc11_growing_bias_not_lipschitz (h : ℝ → ℝ) (degrees : ℕ → ℕ)
    (hd : StrictMono degrees)
    (hg : ∀ m : ℕ, 1 ≤ m → (m : ℝ)/4 ≤ biasFunctional uniformMargins (degrees m) h) :
    ¬ (∃ L : ℝ, ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |h x-h y| ≤ L*|x-y|) := by
  rintro ⟨L,hL⟩
  have hLp : 0 ≤ L := by
    have h := hL 0 (by norm_num) 1 (by norm_num)
    norm_num at h
    exact (abs_nonneg _).trans h
  obtain ⟨m,hm⟩ := exists_nat_gt (32*L+4)
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) < m := by linarith
    exact_mod_cast this.le
  have hd1 : 1 ≤ degrees m := hm1.trans (hd.id_le m)
  have hb := lipschitz_bias_bounded h L hLp hL (degrees m) hd1
  have hg' := hg m hm1
  have ha := le_abs_self (biasFunctional uniformMargins (degrees m) h)
  linarith

/-- All clauses for one fixed witness, including the continuity limit and failure of Lipschitzness. -/
theorem tc11_fixed_bad_mean_properties :
    ∃ h : ℝ → ℝ, ∃ degrees : ℕ → ℕ,
      ContinuousOn h (Set.Icc (-1) 1) ∧ h 0 = 0 ∧
      (∀ x ∈ Set.Icc (-1) 1, |h x| ≤ 1/12) ∧ StrictMono degrees ∧
      (∀ m, 1 ≤ m → biasFunctional uniformMargins (degrees m) h ≥ (m : ℝ)/4) ∧
      (∀ J, 1 ≤ J → populationCoefficient uniformMargins J (fun x => 1/2+h x) = biasFunctional uniformMargins J h) ∧
      Tendsto (fun m => populationCoefficient uniformMargins (degrees m) (fun x => 1/2+h x)) atTop atTop ∧
      ¬ Tendsto (fun J => populationCoefficient uniformMargins J (fun x => 1/2+h x)) atTop (nhds 0) ∧
      Tendsto (populationRD uniformMargins (fun x => 1/2+h x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      (∀ x ∈ Set.Icc (-1) 1, 5/12 ≤ 1/2+h x ∧ 1/2+h x ≤ 7/12) ∧
      ¬ (∃ L : ℝ, ∀ x ∈ Set.Icc (-1) 1, ∀ x' ∈ Set.Icc (-1) 1, |h x-h x'| ≤ L*|x-x'|) := by
  obtain ⟨h,degrees,hc,h0,hb,hd,hg,hfwl⟩ := fixed_bad_mean_unconditional
  have hlim : Tendsto (fun m => populationCoefficient uniformMargins (degrees m)
      (fun x => 1/2+h x)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    obtain ⟨N,hN⟩ := exists_nat_gt (4*B+4)
    filter_upwards [eventually_ge_atTop (max N 1)] with m hm
    have hm1 : 1 ≤ m := (le_max_right N 1).trans hm
    have hmc : (N : ℝ) ≤ m := by exact_mod_cast (le_max_left N 1).trans hm
    rw [hfwl _ (hm1.trans (hd.id_le m))]
    linarith [hg m hm1]
  have hnot : ¬ Tendsto (fun J => populationCoefficient uniformMargins J (fun x => 1/2+h x))
      atTop (nhds 0) := by
    intro hz
    have hsmall := (tendsto_order.mp (hz.comp hd.tendsto_atTop)).2 1 (by norm_num)
    have hlarge := (tendsto_atTop.mp hlim) 2
    obtain ⟨m,hm⟩ := (hsmall.and hlarge).exists
    simp only [Function.comp_apply] at hm
    linarith [hm.1,hm.2]
  refine ⟨h,degrees,hc.continuousOn,h0,hb,hd,hg,hfwl,hlim,hnot,
    populationRD_continuous_limit _ (continuous_const.add hc),?_,
    tc11_growing_bias_not_lipschitz h degrees hd hg⟩
  intro x hx
  have hh := abs_le.mp (hb x hx)
  constructor <;> linarith [hh.1,hh.2]

end
end AronowAudit.P023.Wave1
