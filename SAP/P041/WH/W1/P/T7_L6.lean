import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W1.P.T7_L6

open MeasureTheory

private theorem student197_integral_enclosure
    (hdensity : SAP.P041.WH.W1.T7_L3)
    (hkernel : SAP.P041.WH.W1.T7_L4)
    (hconstant : SAP.P041.WH.W1.T7_L5)
    (x : ℝ) (hx : 0 ≤ x)
    (h25 : 0 ≤ SAP.P041.Student197IntegratedW1 25 x) :
    1 - 2 * (0.39843633174607 : ℝ) * SAP.P041.Student197IntegratedW1 24 x ≤
        SAP.P041.Student197TailW1 x ∧
      SAP.P041.Student197TailW1 x ≤
        1 - 2 * (0.39843633174605 : ℝ) * SAP.P041.Student197IntegratedW1 25 x := by
  let C : ℝ := SAP.P041.Student197ConstantW1
  let K : ℝ → ℝ := fun t => 1 / (1 + t ^ 2 / 197) ^ 99
  have hClo : (0.39843633174605 : ℝ) ≤ C := hconstant.1
  have hChi : C ≤ (0.39843633174607 : ℝ) := hconstant.2
  have hCnonneg : 0 ≤ C := by dsimp [C]; linarith
  have hden : SAP.P041.Student197DensityW1 = fun t => C * K t := by
    funext t
    rw [hdensity t]
    dsimp [C, K]
    ring
  have hP : SAP.P041.Student197TailW1 x =
      1 - (2 * C) * (∫ t in (0 : ℝ)..x, K t) := by
    unfold SAP.P041.Student197TailW1
    rw [abs_of_nonneg hx, hden, intervalIntegral.integral_const_mul]
    ring
  have hK : Continuous K := by
    dsimp [K]
    exact continuous_const.div (by fun_prop) (fun t =>
      (pow_pos (by positivity : (0 : ℝ) < 1 + t ^ 2 / 197) 99).ne')
  have hT25 : Continuous (fun t : ℝ =>
      SAP.P041.Student197TaylorW1 25 (t ^ 2 / 197)) := by
    unfold SAP.P041.Student197TaylorW1
    fun_prop
  have hT24 : Continuous (fun t : ℝ =>
      SAP.P041.Student197TaylorW1 24 (t ^ 2 / 197)) := by
    unfold SAP.P041.Student197TaylorW1
    fun_prop
  have hlo := intervalIntegral.integral_mono_on (μ := volume) hx
    (hT25.intervalIntegrable _ _) (hK.intervalIntegrable _ _)
    (fun t _ => (hkernel (t ^ 2 / 197) (by positivity)).1)
  have hhi := intervalIntegral.integral_mono_on (μ := volume) hx
    (hK.intervalIntegrable _ _) (hT24.intervalIntegrable _ _)
    (fun t _ => (hkernel (t ^ 2 / 197) (by positivity)).2)
  rw [SAP.P041.WH.W1.student197_polynomial_integral 25 x] at hlo
  rw [SAP.P041.WH.W1.student197_polynomial_integral 24 x] at hhi
  have hI0 : 0 ≤ (∫ t in (0 : ℝ)..x, K t) := by
    linarith [hlo]
  have hmulHi : C * (∫ t in (0 : ℝ)..x, K t) ≤
      (0.39843633174607 : ℝ) * SAP.P041.Student197IntegratedW1 24 x := by
    calc
      C * (∫ t in (0 : ℝ)..x, K t) ≤
          (0.39843633174607 : ℝ) * (∫ t in (0 : ℝ)..x, K t) :=
        mul_le_mul_of_nonneg_right hChi hI0
      _ ≤ (0.39843633174607 : ℝ) * SAP.P041.Student197IntegratedW1 24 x :=
        mul_le_mul_of_nonneg_left hhi (by norm_num)
  have hmulLo : (0.39843633174605 : ℝ) *
      SAP.P041.Student197IntegratedW1 25 x ≤
        C * (∫ t in (0 : ℝ)..x, K t) := by
    calc
      (0.39843633174605 : ℝ) * SAP.P041.Student197IntegratedW1 25 x ≤
          C * SAP.P041.Student197IntegratedW1 25 x :=
        mul_le_mul_of_nonneg_right hClo h25
      _ ≤ C * (∫ t in (0 : ℝ)..x, K t) :=
        mul_le_mul_of_nonneg_left hlo hCnonneg
  constructor
  · rw [hP]
    nlinarith [hmulHi]
  · rw [hP]
    nlinarith [hmulLo]

end SAP.P041.WH.W1.P.T7_L6

theorem SAP.P041.WH.W1.T7_L6_proof : SAP.P041.WH.W1.T7_L6 := by
  intro hdensity hkernel hconstant
  have hpa : 0 ≤ SAP.P041.Student197IntegratedW1 25 (64 / 129 : ℝ) := by
    norm_num [SAP.P041.Student197IntegratedW1, Finset.sum_range_succ, Nat.choose]
  have ha := SAP.P041.WH.W1.P.T7_L6.student197_integral_enclosure
    hdensity hkernel hconstant (64 / 129 : ℝ) (by norm_num) hpa
  have hpb : 0 ≤ SAP.P041.Student197IntegratedW1 25 (1 : ℝ) := by
    norm_num [SAP.P041.Student197IntegratedW1, Finset.sum_range_succ, Nat.choose]
  have hb := SAP.P041.WH.W1.P.T7_L6.student197_integral_enclosure
    hdensity hkernel hconstant (1 : ℝ) (by norm_num) hpb
  have hpc : 0 ≤ SAP.P041.Student197IntegratedW1 25 (2.6005 : ℝ) := by
    norm_num [SAP.P041.Student197IntegratedW1, Finset.sum_range_succ, Nat.choose]
  have hc := SAP.P041.WH.W1.P.T7_L6.student197_integral_enclosure
    hdensity hkernel hconstant (2.6005 : ℝ) (by norm_num) hpc
  have hpd : 0 ≤ SAP.P041.Student197IntegratedW1 25 (2.6015 : ℝ) := by
    norm_num [SAP.P041.Student197IntegratedW1, Finset.sum_range_succ, Nat.choose]
  have hd := SAP.P041.WH.W1.P.T7_L6.student197_integral_enclosure
    hdensity hkernel hconstant (2.6015 : ℝ) (by norm_num) hpd
  unfold SAP.P041.Student197EndpointsW1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hh := ha.1
    have hnum : (0.615 : ℝ) < 1 - 2 * 0.39843633174607 *
        SAP.P041.Student197IntegratedW1 24 (64 / 129 : ℝ) := by
      norm_num [SAP.P041.Student197IntegratedW1, Finset.sum_range_succ, Nat.choose]
    exact lt_of_lt_of_le hnum hh
  · have hh := ha.2
    have hnum : 1 - 2 * 0.39843633174605 *
        SAP.P041.Student197IntegratedW1 25 (64 / 129 : ℝ) < (0.625 : ℝ) := by
      norm_num [SAP.P041.Student197IntegratedW1, Finset.sum_range_succ, Nat.choose]
    exact lt_of_le_of_lt hh hnum
  · have hh := hb.1
    have hnum : (0.10 : ℝ) < 1 - 2 * 0.39843633174607 *
        SAP.P041.Student197IntegratedW1 24 (1 : ℝ) := by
      norm_num [SAP.P041.Student197IntegratedW1, Finset.sum_range_succ, Nat.choose]
    exact lt_of_lt_of_le hnum hh
  · have hh := hc.1
    have hnum : (0.01 : ℝ) < 1 - 2 * 0.39843633174607 *
        SAP.P041.Student197IntegratedW1 24 (2.6005 : ℝ) := by
      norm_num [SAP.P041.Student197IntegratedW1, Finset.sum_range_succ, Nat.choose]
    exact lt_of_lt_of_le hnum hh
  · have hh := hd.2
    have hnum : 1 - 2 * 0.39843633174605 *
        SAP.P041.Student197IntegratedW1 25 (2.6015 : ℝ) < (0.01 : ℝ) := by
      norm_num [SAP.P041.Student197IntegratedW1, Finset.sum_range_succ, Nat.choose]
    exact lt_of_le_of_lt hh hnum
