import SAP.P031.WH.W1.Leaves
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable section

namespace SAP.P031.WH.W1.P.T6_L5

lemma gaussian_interval_integral_lower :
    5 / (3 * Real.sqrt (2 * Real.pi)) ≤
      ∫ x in Set.Ioc (-1 : ℝ) 1, ProbabilityTheory.gaussianPDFReal 0 1 x := by
  let c : ℝ := Real.sqrt (2 * Real.pi)
  have hc : 0 < c := by positivity
  have hpoly : (∫ x in (-1 : ℝ)..1, (1 - x ^ 2 / 2)) = 5 / 3 := by
    calc
      (∫ x in (-1 : ℝ)..1, (1 - x ^ 2 / 2)) =
          (∫ _ in (-1 : ℝ)..1, (1 : ℝ)) -
            (1 / 2 : ℝ) * (∫ x in (-1 : ℝ)..1, x ^ 2) := by
        rw [intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _)]
        rw [show (fun x : ℝ => x ^ 2 / 2) = fun x => (1 / 2 : ℝ) * x ^ 2 by
          funext x
          ring]
        rw [intervalIntegral.integral_const_mul]
      _ = 5 / 3 := by
        rw [intervalIntegral.integral_const, integral_pow]
        norm_num
  have hloweval :
      (∫ x in (-1 : ℝ)..1, (1 - x ^ 2 / 2) / c) = 5 / (3 * c) := by
    calc
      (∫ x in (-1 : ℝ)..1, (1 - x ^ 2 / 2) / c) =
          c⁻¹ * (∫ x in (-1 : ℝ)..1, (1 - x ^ 2 / 2)) := by
        rw [show (fun x : ℝ => (1 - x ^ 2 / 2) / c) =
            fun x => c⁻¹ * (1 - x ^ 2 / 2) by
          funext x
          ring]
        rw [intervalIntegral.integral_const_mul]
      _ = 5 / (3 * c) := by rw [hpoly]; ring
  have hmono :
      (∫ x in (-1 : ℝ)..1, (1 - x ^ 2 / 2) / c) ≤
        ∫ x in (-1 : ℝ)..1, ProbabilityTheory.gaussianPDFReal 0 1 x := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by
        unfold ProbabilityTheory.gaussianPDFReal
        fun_prop) _ _
    · intro x hx
      have hprod : 0 ≤ (1 - x) * (1 + x) :=
        mul_nonneg (by linarith [hx.2]) (by linarith [hx.1])
      have hx2 : x ^ 2 ≤ 1 := by nlinarith [hprod]
      have he := Real.add_one_le_exp (-(x ^ 2) / 2)
      have hfactor : 0 ≤ c⁻¹ := by positivity
      calc
        (1 - x ^ 2 / 2) / c = c⁻¹ * (1 - x ^ 2 / 2) := by ring
        _ ≤ c⁻¹ * Real.exp (-(x ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hfactor
        _ = ProbabilityTheory.gaussianPDFReal 0 1 x := by
          simp [ProbabilityTheory.gaussianPDFReal, c]
  calc
    5 / (3 * Real.sqrt (2 * Real.pi)) =
        ∫ x in (-1 : ℝ)..1, (1 - x ^ 2 / 2) / c := by
      rw [hloweval]
    _ ≤ ∫ x in (-1 : ℝ)..1, ProbabilityTheory.gaussianPDFReal 0 1 x := hmono
    _ = ∫ x in Set.Ioc (-1 : ℝ) 1, ProbabilityTheory.gaussianPDFReal 0 1 x :=
      (intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1))

end SAP.P031.WH.W1.P.T6_L5

theorem SAP.P031.WH.W1.T6_L5_proof : SAP.P031.WH.W1.T6_L5 := by
  have hhalf : (1 / 2 : ℝ) ≤ SAP.P031.normalCDF 1 := by
    calc
      (1 / 2 : ℝ) = SAP.P031.normalCDF 0 := by
        simpa [SAP.P031.normalCDF] using
          AronowAudit.P053.NormalCompletion.normal_cdf_zero.symm
      _ ≤ SAP.P031.normalCDF 1 := by
        change ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) 0 ≤
          ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) 1
        exact ProbabilityTheory.monotone_cdf (ProbabilityTheory.gaussianReal 0 1)
          (by norm_num)
  have hsym := AronowAudit.P053.NormalCompletion.normal_cdf_neg (1 : ℝ)
  have hmass :
      ProbabilityTheory.gaussianReal 0 1 (Set.Ioc (-1 : ℝ) 1) =
        ENNReal.ofReal (2 * SAP.P031.normalCDF 1 - 1) := by
    calc
      ProbabilityTheory.gaussianReal 0 1 (Set.Ioc (-1 : ℝ) 1) =
          (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)).measure
            (Set.Ioc (-1 : ℝ) 1) := by
        exact congrArg (fun ν : Measure ℝ => ν (Set.Ioc (-1 : ℝ) 1))
          (ProbabilityTheory.measure_cdf
            (ProbabilityTheory.gaussianReal 0 1)).symm
      _ = ENNReal.ofReal
          (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) 1 -
            ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-1)) :=
          (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)).measure_Ioc (-1) 1
      _ = ENNReal.ofReal (2 * SAP.P031.normalCDF 1 - 1) := by
        rw [hsym]
        congr 1
        simp only [SAP.P031.normalCDF]
        ring
  have harg : 0 ≤ 2 * SAP.P031.normalCDF 1 - 1 := by linarith
  have hmassReal :
      (ProbabilityTheory.gaussianReal 0 1 (Set.Ioc (-1 : ℝ) 1)).toReal =
        2 * SAP.P031.normalCDF 1 - 1 := by
    rw [hmass, ENNReal.toReal_ofReal harg]
  have hintegral :
      (ProbabilityTheory.gaussianReal 0 1 (Set.Ioc (-1 : ℝ) 1)).toReal =
        ∫ x in Set.Ioc (-1 : ℝ) 1, ProbabilityTheory.gaussianPDFReal 0 1 x := by
    rw [ProbabilityTheory.gaussianReal_apply_eq_integral 0
      (by norm_num : (1 : NNReal) ≠ 0) (Set.Ioc (-1 : ℝ) 1)]
    rw [ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Ioc
      (fun x _ => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x)
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hsqrt : Real.sqrt (2 * Real.pi) < 3 := by
    calc
      Real.sqrt (2 * Real.pi) < Real.sqrt 9 :=
        (Real.sqrt_lt_sqrt_iff (by positivity)).2 (by nlinarith [hpi])
      _ = 3 := by norm_num
  have hnumeric : (1 / 2 : ℝ) < 5 / (3 * Real.sqrt (2 * Real.pi)) := by
    have hden : 0 < 3 * Real.sqrt (2 * Real.pi) := by positivity
    rw [lt_div_iff₀ hden]
    nlinarith
  calc
    (1 / 2 : ℝ) < 5 / (3 * Real.sqrt (2 * Real.pi)) := hnumeric
    _ ≤ ∫ x in Set.Ioc (-1 : ℝ) 1,
          ProbabilityTheory.gaussianPDFReal 0 1 x :=
            SAP.P031.WH.W1.P.T6_L5.gaussian_interval_integral_lower
    _ = 2 * SAP.P031.normalCDF 1 - 1 := hintegral.symm.trans hmassReal
