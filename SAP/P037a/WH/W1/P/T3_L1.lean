import SAP.P037a.WH.W1.Leaves
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W1.P.T3_L1

open MeasureTheory ProbabilityTheory Set
open scoped Topology

lemma wholeNormalCDF_integral_Iic (x : ℝ) :
    SAP.P037a.wholeNormalCDF x =
      ∫ y in Set.Iic x, ProbabilityTheory.gaussianPDFReal 0 1 y := by
  rw [SAP.P037a.wholeNormalCDF, ProbabilityTheory.cdf_eq_real,
    MeasureTheory.measureReal_def,
    ProbabilityTheory.gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0)]
  exact ENNReal.toReal_ofReal
    (integral_nonneg (fun y => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 y))

lemma gaussianPDFReal_standard (x : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 1 x =
      (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-x^2/2) := by
  simp [ProbabilityTheory.gaussianPDFReal]

lemma interval_gaussianPDFReal_eq (z : ℝ) :
    (∫ t in (0:ℝ)..z, ProbabilityTheory.gaussianPDFReal 0 1 t) =
      (1 / Real.sqrt (2 * Real.pi)) *
        (∫ t in (0:ℝ)..z, Real.exp (-t^2/2)) := by
  calc
    _ = ∫ t in (0:ℝ)..z,
        (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-t^2/2) := by
          congr 1
          funext t
          exact gaussianPDFReal_standard t
    _ = _ := intervalIntegral.integral_const_mul _ _

end SAP.P037a.WH.W1.P.T3_L1

theorem SAP.P037a.WH.W1.T3_L1_proof : SAP.P037a.WH.W1.T3_L1 := by
  intro z hz
  have hinterval := intervalIntegral.integral_Iic_sub_Iic
    (ProbabilityTheory.integrable_gaussianPDFReal 0 1).integrableOn
    (ProbabilityTheory.integrable_gaussianPDFReal 0 1).integrableOn
    (a := (0:ℝ)) (b := z)
  change (∫ y in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 y) -
      (∫ y in Set.Iic (0:ℝ), ProbabilityTheory.gaussianPDFReal 0 1 y) = _ at hinterval
  rw [← SAP.P037a.WH.W1.P.T3_L1.wholeNormalCDF_integral_Iic z,
    ← SAP.P037a.WH.W1.P.T3_L1.wholeNormalCDF_integral_Iic 0] at hinterval
  have hzero : SAP.P037a.wholeNormalCDF 0 = 1/2 := by
    simpa [SAP.P037a.wholeNormalCDF] using
      AronowAudit.P053.NormalCompletion.normal_cdf_zero
  rw [hzero] at hinterval
  change SAP.P037a.wholeNormalCDF z - 1/2 =
      ∫ t in (0:ℝ)..z, ProbabilityTheory.gaussianPDFReal 0 1 t at hinterval
  rw [SAP.P037a.WH.W1.P.T3_L1.interval_gaussianPDFReal_eq z] at hinterval
  linarith
