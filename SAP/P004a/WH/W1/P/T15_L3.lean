import SAP.P004a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T15_L3

open MeasureTheory Set
open scoped ENNReal

private theorem midpoint_bounds (a b : ℝ) (hab : a < b) :
    a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b := by
  constructor <;> linarith

private theorem radial_delta_pos (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    0 < b ^ 2 - a ^ 2 := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  nlinarith [sq_pos_of_pos (sub_pos.mpr hab)]

private theorem radial_density_midpoint (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    (volume.withDensity (fun r : ℝ => ENNReal.ofReal
      (if a ≤ r ∧ r ≤ b then 2*r/(b^2-a^2) else 0)))
      (Set.Iic ((a+b)/2)) =
        ENNReal.ofReal ((((a+b)/2)^2-a^2)/(b^2-a^2)) := by
  let m : ℝ := (a+b)/2
  have hm := midpoint_bounds a b hab
  have hΔ := radial_delta_pos a b ha hab
  have hind : (fun r : ℝ => ENNReal.ofReal
      (if a ≤ r ∧ r ≤ b then 2*r/(b^2-a^2) else 0)) =
      (Set.Icc a b).indicator (fun r : ℝ => ENNReal.ofReal (2*r/(b^2-a^2))) := by
    funext r
    by_cases hr : a ≤ r ∧ r ≤ b <;>
      simp [Set.indicator, Set.mem_Icc, hr]
  rw [withDensity_apply _ measurableSet_Iic, hind,
    setLIntegral_indicator measurableSet_Icc]
  have hset : Set.Icc a b ∩ Set.Iic m = Set.Icc a m := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨⟨har, hrb⟩, hrm⟩
      exact ⟨har, hrm⟩
    · rintro ⟨har, hrm⟩
      exact ⟨⟨har, hrm.trans hm.2⟩, hrm⟩
  rw [hset]
  have hg : IntegrableOn (fun r : ℝ => 2*r/(b^2-a^2)) (Set.Icc a m) := by
    exact (by fun_prop : Continuous (fun r : ℝ => 2*r/(b^2-a^2))).integrableOn_Icc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc a m)]
      (fun r : ℝ => 2*r/(b^2-a^2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact div_nonneg (mul_nonneg (by norm_num) (ha.trans hr.1)) hΔ.le
  rw [← ofReal_integral_eq_lintegral_ofReal hg hnonneg,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hm.1,
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    integral_id]
  change ENNReal.ofReal (2 * ((m ^ 2 - a ^ 2) / 2) / (b ^ 2 - a ^ 2)) = _
  congr 1
  dsimp [m]
  ring

private theorem uniform_radial_midpoint (a b : ℝ) (hab : a < b) :
    w1UniformRadial a b (Set.Iic ((a+b)/2)) = ENNReal.ofReal (1/2) := by
  have hm := midpoint_bounds a b hab
  unfold w1UniformRadial
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Icc a b ∩ Set.Iic ((a+b)/2) = Set.Icc a ((a+b)/2) := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨⟨har, hrb⟩, hrm⟩
      exact ⟨har, hrm⟩
    · rintro ⟨har, hrm⟩
      exact ⟨⟨har, hrm.trans hm.2⟩, hrm⟩
  rw [Set.inter_comm, hset, Real.volume_Icc]
  have hbd : 0 < b-a := sub_pos.mpr hab
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(b-a))]
  congr 1
  have : (a+b)/2-a = (b-a)/2 := by ring
  rw [this]
  field_simp

end SAP.P004a.WH.W1.P.T15_L3

theorem SAP.P004a.WH.W1.T15_L3_proof : SAP.P004a.WH.W1.T15_L3 := by
  intro a b ha hab
  exact ⟨SAP.P004a.WH.W1.P.T15_L3.radial_density_midpoint a b ha hab,
    SAP.P004a.WH.W1.P.T15_L3.uniform_radial_midpoint a b hab⟩
