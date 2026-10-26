import AronowAudit.External.Causalean.Stat.OrderStatistic.Moments
import AronowAudit.P009.Wave1.Lib.SimulationRecovered

/-! Positive scaling of Causalean's uniform spacing moments to the normalized
uniform laws used in P009. -/
namespace AronowAudit.P009.Wave1
open MeasureTheory
open Causalean.Stat.OrderStatistic
noncomputable section

/-- Multiplication sends the unit uniform law to the normalized law on `[0,L]`. -/
theorem tc01_uniform_scale (L : ℝ) (hL : 0 < L) :
    uniform01.map (fun u => L * u) = t23_uniform L := by
  have hpre : (fun u : ℝ => L * u) ⁻¹' Set.Icc 0 L = Set.Icc 0 1 := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> nlinarith
  change (volume.restrict (Set.Icc 0 1)).map (fun u => L * u) = _
  rw [← hpre, ← Measure.restrict_map (measurable_const_mul L) measurableSet_Icc,
    Real.map_volume_mul_left hL.ne', Measure.restrict_smul]
  simp only [t23_uniform, abs_of_pos (inv_pos.mpr hL), ENNReal.ofReal_inv_of_pos hL]

/-- Coordinatewise positive scaling of the complete iid law. -/
theorem tc01_cube_scale (n : ℕ) (L : ℝ) (hL : 0 < L) :
    (iidSample uniform01 n).map (fun x i => L * x i) = t23_cube n L := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
  change (Measure.pi (fun _ : Fin n => uniform01)).map (fun x i => L * x i) = _
  rw [Measure.pi_map_pi (fun _ => (measurable_const_mul L).aemeasurable)]
  simp only [tc01_uniform_scale L hL, t23_cube]

/-- Sorted coordinate values commute with positive scaling, including on ties. -/
theorem tc01_sorted_scale (n : ℕ) (L : ℝ) (hL : 0 < L) (x : Fin n → ℝ) :
    sortedSample n (fun i => L * x i) = fun i => L * sortedSample n x i := by
  have hm : Monotone ((fun i => L * x i) ∘ Tuple.sort x) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (Tuple.monotone_sort x hij) hL.le
  exact (Tuple.comp_sort_eq_comp_iff_monotone.mpr hm).symm

theorem tc01_gap_scale (n k : ℕ) (L : ℝ) (hL : 0 < L) (x : Fin n → ℝ) :
    sortedGap n k (fun i => L * x i) = L * sortedGap n k x := by
  by_cases hk : k + 1 < n
  · simp only [sortedGap, dif_pos hk, tc01_sorted_scale n L hL]
    ring
  · simp [sortedGap, hk]

/-- The actual second moment under normalized iid uniform sampling on `[0,L]`. -/
theorem scaled_uniform_gap_moment (n k : ℕ) (hk : k + 1 < n)
    (L : ℝ) (hL : 0 < L) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin n =>
      (ENNReal.ofReal L)⁻¹ • MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) L))
    Integrable (fun x => (Causalean.Stat.OrderStatistic.sortedGap n k x)^2) μ ∧
    (∫ x, (Causalean.Stat.OrderStatistic.sortedGap n k x)^2 ∂μ) =
      2 * L^2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  change Integrable _ (t23_cube n L) ∧ _
  constructor
  · simpa only [sortedGap, dif_pos hk, sortedSample, Function.comp_apply, t23_gap]
      using t23_gap_integrable L hL k hk
  · change (∫ x, (sortedGap n k x)^2 ∂t23_cube n L) =
      2 * L^2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))
    let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
      MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.mulLeft₀ L hL.ne')
    have he : (iidSample uniform01 n).map e = t23_cube n L := tc01_cube_scale n L hL
    rw [← he, integral_map_equiv]
    change (∫ x, (sortedGap n k (fun i => L * x i)) ^ 2 ∂iidSample uniform01 n) = _
    simp_rw [tc01_gap_scale n k L hL, mul_pow]
    rw [integral_const_mul, uniform_gap_second_moment n k hk]
    push_cast
    ring

/-- The uniform spacing second-moment identity. -/
theorem tc01_uniform_spacing_second_moment : t23_UniformSpacingSecondMoment := by
  intro n _ L hL j hj
  simpa only [sortedGap, dif_pos hj, sortedSample, Function.comp_apply,
    t23_gap, t23_cube, t23_uniform] using scaled_uniform_gap_moment n j hj L hL

end
end AronowAudit.P009.Wave1
