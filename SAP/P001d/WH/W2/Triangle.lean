import SAP.P001d.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W2

theorem triangle_support : Function.support wholeTrianglePDF ⊆ Set.Ioc (5/4 : ℝ) (7/4) := by
  intro x hx
  change wholeTrianglePDF x ≠ 0 at hx
  constructor
  · by_contra h
    have hh : x ≤ 5/4 := le_of_not_gt h
    apply hx
    unfold wholeTrianglePDF
    apply max_eq_left
    nlinarith [neg_le_abs (x-3/2)]
  · by_contra h
    have hh : 7/4 < x := lt_of_not_ge h
    apply hx
    unfold wholeTrianglePDF
    apply max_eq_left
    nlinarith [le_abs_self (x-3/2)]

theorem triangle_integral : Integrable wholeTrianglePDF volume ∧ (∫ x, wholeTrianglePDF x) = 1 := by
  have hc : Continuous wholeTrianglePDF := by unfold wholeTrianglePDF; fun_prop
  have hi : Integrable wholeTrianglePDF volume :=
    (integrableOn_iff_integrable_of_support_subset
      (triangle_support.trans Set.Ioc_subset_Icc_self)).mp (hc.integrableOn_Icc)
  refine ⟨hi, ?_⟩
  rw [← intervalIntegral.integral_eq_integral_of_support_subset triangle_support]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (5/4 : ℝ) (3/2)) (hc.intervalIntegrable (3/2 : ℝ) (7/4))]
  have hl : (∫ x in (5/4 : ℝ)..(3/2), wholeTrianglePDF x) =
      ∫ x in (5/4 : ℝ)..(3/2), (16*x-20) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (5/4 : ℝ) (3/2) := by simpa only [Set.uIcc_of_le (by norm_num : (5/4 : ℝ) ≤ 3/2)] using hx
    rw [wholeTrianglePDF, abs_of_nonpos (by linarith [hx'.2] : x-3/2 ≤ 0), max_eq_right (by linarith [hx'.1])]
    ring
  have hr : (∫ x in (3/2 : ℝ)..(7/4), wholeTrianglePDF x) =
      ∫ x in (3/2 : ℝ)..(7/4), (28-16*x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (3/2 : ℝ) (7/4) := by simpa only [Set.uIcc_of_le (by norm_num : (3/2 : ℝ) ≤ 7/4)] using hx
    rw [wholeTrianglePDF, abs_of_nonneg (by linarith [hx'.1] : 0 ≤ x-3/2), max_eq_right (by linarith [hx'.2])]
    ring
  rw [hl, hr, intervalIntegral.integral_sub ((by fun_prop : Continuous (fun x : ℝ => 16*x)).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun x : ℝ => 16*x)).intervalIntegrable _ _)]
  have hl16 : (∫ x in (5/4 : ℝ)..(3/2), (16 : ℝ)*x) =
      16 * ∫ x in (5/4 : ℝ)..(3/2), x := intervalIntegral.integral_const_mul 16 (fun x : ℝ => x)
  have hr16 : (∫ x in (3/2 : ℝ)..(7/4), (16 : ℝ)*x) =
      16 * ∫ x in (3/2 : ℝ)..(7/4), x := intervalIntegral.integral_const_mul 16 (fun x : ℝ => x)
  rw [hl16, hr16]
  norm_num [integral_id]

theorem triangle_probability_witness : IsProbabilityMeasure wholeTriangleLaw := by
  constructor
  rw [wholeTriangleLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  · rw [← ofReal_integral_eq_lintegral_ofReal triangle_integral.1]
    · rw [triangle_integral.2, ENNReal.ofReal_one]
    · exact Eventually.of_forall (fun x => le_max_left _ _)


/-- Every piece of the explicit triangular-law certificate is proved. -/
theorem triangle_certificate :
    Integrable wholeTrianglePDF volume ∧ (∫ x, wholeTrianglePDF x) = 1 ∧
    IsProbabilityMeasure wholeTriangleLaw ∧
    (∀ᵐ x ∂wholeTriangleLaw, x ∈ Set.Icc (5/4 : ℝ) (7/4)) ∧
    cdf wholeTriangleLaw id 0 = 0 := by
  have hm : Measurable (fun x => ENNReal.ofReal (wholeTrianglePDF x)) := by
    unfold wholeTrianglePDF
    fun_prop
  have ha : ∀ᵐ x ∂wholeTriangleLaw, x ∈ Set.Icc (5/4 : ℝ) (7/4) := by
    apply (ae_withDensity_iff hm).mpr
    exact Eventually.of_forall (fun x hx => Set.Ioc_subset_Icc_self (triangle_support (by
      intro hz
      exact hx (by rw [hz, ENNReal.ofReal_zero]))))
  have hz : wholeTriangleLaw (Set.Iic 0) = 0 := by
    rw [wholeTriangleLaw, withDensity_apply_eq_zero hm]
    have he : {x : ℝ | ENNReal.ofReal (wholeTrianglePDF x) ≠ 0} ∩ Set.Iic 0 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hx0⟩
      have hs := triangle_support (show wholeTrianglePDF x ≠ 0 from fun h => hx (by rw [h, ENNReal.ofReal_zero]))
      have hle : x ≤ 0 := hx0
      linarith [hs.1]
    rw [he, measure_empty]
  refine ⟨triangle_integral.1, triangle_integral.2, triangle_probability_witness, ha, ?_⟩
  change (wholeTriangleLaw (Set.Iic 0)).toReal = 0
  rw [hz, ENNReal.toReal_zero]

end SAP.P001d.WH.W2
