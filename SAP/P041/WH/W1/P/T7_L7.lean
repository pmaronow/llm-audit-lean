import SAP.P041.WH.W1.Leaves
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

theorem SAP.P041.WH.W1.T7_L7_proof : SAP.P041.WH.W1.T7_L7 := by
  constructor
  · have hdRef : Continuous (AronowAudit.P040.studentReferenceDensity 197) :=
      (AronowAudit.P040.student_density_regular
        (nu := 197) (by norm_num : (0 : ℝ) < 197)).1
    have hdEq : SAP.P041.Student197DensityW1 =
        AronowAudit.P040.studentReferenceDensity 197 :=
      funext SAP.P041.WH.W1.student197_density_eq_reference
    have hd : Continuous SAP.P041.Student197DensityW1 := by
      rw [hdEq]
      exact hdRef
    have hInt : Continuous (fun x : ℝ =>
        ∫ t in (0 : ℝ)..|x|, SAP.P041.Student197DensityW1 t) := by
      have hF : Differentiable ℝ (fun u : ℝ =>
          ∫ t in (0 : ℝ)..u, SAP.P041.Student197DensityW1 t) :=
        intervalIntegral.differentiable_integral_of_continuous hd
      exact hF.continuous.comp continuous_abs
    change Continuous (fun x : ℝ =>
      1 - 2 * ∫ t in (0 : ℝ)..|x|, SAP.P041.Student197DensityW1 t)
    exact continuous_const.sub (continuous_const.mul hInt)
  · have hd : Continuous SAP.P041.Student197DensityW1 := by
      have hdRef : Continuous (AronowAudit.P040.studentReferenceDensity 197) :=
        (AronowAudit.P040.student_density_regular
          (nu := 197) (by norm_num : (0 : ℝ) < 197)).1
      have hdEq : SAP.P041.Student197DensityW1 =
          AronowAudit.P040.studentReferenceDensity 197 :=
        funext SAP.P041.WH.W1.student197_density_eq_reference
      rw [hdEq]
      exact hdRef
    have hdpos (t : ℝ) : 0 < SAP.P041.Student197DensityW1 t := by
      have htop : 0 < Real.Gamma (((197 : ℝ) + 1) / 2) :=
        Real.Gamma_pos_of_pos (by norm_num)
      have hbottom : 0 < Real.Gamma ((197 : ℝ) / 2) :=
        Real.Gamma_pos_of_pos (by norm_num)
      have hroot : 0 < Real.sqrt ((197 : ℝ) * Real.pi) :=
        Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)
      have hbase : 0 < 1 + t ^ 2 / (197 : ℝ) := by positivity
      rw [SAP.P041.WH.W1.student197_density_eq_reference]
      unfold AronowAudit.P040.studentReferenceDensity
      exact mul_pos
        (div_pos htop (mul_pos hroot hbottom))
        (Real.rpow_pos_of_pos hbase _)
    intro a ha b hb hab
    have hInt0a : IntervalIntegrable
        SAP.P041.Student197DensityW1 volume 0 a := hd.intervalIntegrable _ _
    have hIntab : IntervalIntegrable
        SAP.P041.Student197DensityW1 volume a b := hd.intervalIntegrable _ _
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hInt0a hIntab
    have hpositive := intervalIntegral.intervalIntegral_pos_of_pos hIntab hdpos hab
    have ha0 : 0 ≤ a := by simpa using ha
    have hb0 : 0 ≤ b := by simpa using hb
    simp only [SAP.P041.Student197TailW1,
      abs_of_nonneg ha0, abs_of_nonneg hb0]
    rw [← hsplit]
    linarith

