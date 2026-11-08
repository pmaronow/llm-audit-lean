import SAP.P017.WH.W2.Leaves
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P017.WH.W2.P.T11_L1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

private theorem density (x : ℝ) :
    gaussianPDFReal 0 1 x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

private theorem density_deriv (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1)
      (-x * gaussianPDFReal 0 1 x) x := by
  have hd := ((hasDerivAt_pow 2 x).const_mul (-(1 / 2 : ℝ))).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  have hf : gaussianPDFReal 0 1 = fun y : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * y ^ 2) :=
    funext density
  simp only [hf]
  convert hd using 1
  norm_num
  ring

theorem second_integrable :
    Integrable (fun x : ℝ => x ^ 2 * gaussianPDFReal 0 1 x) := by
  have hi := (integrable_rpow_mul_exp_neg_mul_sq
    (b := (1 / 2 : ℝ)) (s := (2 : ℝ)) (by norm_num) (by norm_num)).const_mul
      (Real.sqrt (2 * Real.pi))⁻¹
  convert hi using 1
  ext x
  rw [density, Real.rpow_two]
  ring

private theorem boundary :
    Tendsto (fun x : ℝ => x * gaussianPDFReal 0 1 x) atTop (𝓝 0) := by
  have hsmall := rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
    (b := (1 / 2 : ℝ)) (by norm_num) (1 : ℝ)
  have he : Tendsto (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0))
  have hz := (hsmall.tendsto_zero_of_tendsto he).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert hz using 1
  · ext x
    rw [density, Real.rpow_one]
    ring
  · ring

private theorem density_tail (a : ℝ) :
    (∫ x in Ioi a, gaussianPDFReal 0 1 x) = SAP.P017.normalCDF (-a) := by
  let γ : Measure ℝ := gaussianReal 0 1
  haveI : NullSingletonClass γ :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  have hmap : γ.map (fun x : ℝ => -x) = γ := by
    simpa only [neg_zero] using
      (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
  have hreflect : γ (Iic (-a)) = γ (Ici a) := by
    conv_lhs => rw [← hmap, Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext x
    simp
  have hatom : γ (Ioi a) = γ (Ici a) :=
    measure_congr (Ioi_ae_eq_Ici' (measure_singleton a))
  have hpdf : γ (Ioi a) = ENNReal.ofReal
      (∫ x in Ioi a, gaussianPDFReal 0 1 x) :=
    gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0) _
  have hnonneg : 0 ≤ ∫ x in Ioi a, gaussianPDFReal 0 1 x :=
    integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x)
  change _ = (γ (Iic (-a))).toReal
  rw [hreflect, ← hatom, hpdf, ENNReal.toReal_ofReal hnonneg]

private theorem second_tail_identity (a : ℝ) :
    (∫ x in Ioi a, x ^ 2 * gaussianPDFReal 0 1 x) =
      a * gaussianPDFReal 0 1 a + SAP.P017.normalCDF (-a) := by
  have hsecond := second_integrable.integrableOn (s := Ioi a)
  have hzero := (integrable_gaussianPDFReal 0 1).integrableOn (s := Ioi a)
  have hd (x : ℝ) : HasDerivAt (fun y => y * gaussianPDFReal 0 1 y)
      (gaussianPDFReal 0 1 x - x ^ 2 * gaussianPDFReal 0 1 x) x := by
    convert (hasDerivAt_id' x).mul (density_deriv x) using 1
    ring
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := a) (fun x _ => hd x) (hzero.sub hsecond) boundary
  rw [integral_sub hzero hsecond, density_tail] at hftc
  linarith

end
end SAP.P017.WH.W2.P.T11_L1

theorem SAP.P017.WH.W2.T11_L1_proof : SAP.P017.WH.W2.T11_L1 := by
  constructor
  · exact SAP.P017.WH.W2.P.T11_L1.second_integrable
  · intro a ha
    exact SAP.P017.WH.W2.P.T11_L1.second_tail_identity a
