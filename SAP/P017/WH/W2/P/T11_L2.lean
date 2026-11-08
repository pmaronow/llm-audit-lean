import SAP.P017.WH.W2.Leaves
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P017.WH.W2.P.T11_L2

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

theorem gaussianPDFReal_zero_one (z : ℝ) :
    gaussianPDFReal 0 1 z =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * z ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

theorem tail_integrand_integrable (n : ℕ) (hn : 1 ≤ n) (σ : ℝ)
    (hσ : 0 < σ) :
    Integrable (SAP.P017.wholeTailIntegrand n σ) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hb : 0 < (n : ℝ) / (2 * σ ^ 2) := by positivity
  have hbase := integrable_rpow_mul_exp_neg_mul_sq
    (b := (n : ℝ) / (2 * σ ^ 2)) hb (s := (2 : ℝ)) (by norm_num)
  have hscaled := hbase.const_mul
    (SAP.P017.sqrtN n / (σ * Real.sqrt (2 * Real.pi)))
  have hscaled' : Integrable (fun x : ℝ =>
      SAP.P017.sqrtN n / (σ * Real.sqrt (2 * Real.pi)) *
        (x ^ 2 * Real.exp (-((n : ℝ) / (2 * σ ^ 2) * x ^ 2)))) := by
    convert hscaled using 1
    ext x
    rw [Real.rpow_two, ← neg_mul]
  have hEq : (fun x : ℝ =>
      SAP.P017.sqrtN n / (σ * Real.sqrt (2 * Real.pi)) *
        (x ^ 2 * Real.exp (-((n : ℝ) / (2 * σ ^ 2) * x ^ 2)))) =
      SAP.P017.wholeTailIntegrand n σ := by
    funext x
    rw [SAP.P017.wholeTailIntegrand]
    have hexp : -((n : ℝ) / (2 * σ ^ 2) * x ^ 2) =
        -(x ^ 2 * (n : ℝ)) / (2 * σ ^ 2) := by
      field_simp [ne_of_gt hσ]
      <;> ring
    rw [hexp]
    ring
  rw [← hEq]
  exact hscaled'

theorem rescale_tail_integral (n : ℕ) (hn : 1 ≤ n) (c σ : ℝ)
    (hσ : 0 < σ) :
    SAP.P017.normalTail n c σ =
      2 * (σ / SAP.P017.sqrtN n) ^ 2 *
        (∫ z in Ioi (c / (σ / SAP.P017.sqrtN n)),
          z ^ 2 * gaussianPDFReal 0 1 z) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hsqrt : 0 < SAP.P017.sqrtN n :=
    Real.sqrt_pos.mpr hnpos
  have hsquare : SAP.P017.sqrtN n ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  let s : ℝ := σ / SAP.P017.sqrtN n
  have hs : 0 < s := div_pos hσ hsqrt
  let F : ℝ → ℝ := fun x =>
    x ^ 2 * (SAP.P017.sqrtN n / (σ * Real.sqrt (2 * Real.pi))) *
      Real.exp (-(x ^ 2 * (n : ℝ)) / (2 * σ ^ 2))
  have hexp (z : ℝ) :
      -((s * z) ^ 2 * (n : ℝ)) / (2 * σ ^ 2) = -(1 / 2 : ℝ) * z ^ 2 := by
    dsimp [s]
    rw [← hsquare]
    field_simp [ne_of_gt hσ, ne_of_gt hsqrt]
    <;> ring
  have hF (z : ℝ) : F (s * z) = s * (z ^ 2 * gaussianPDFReal 0 1 z) := by
    dsimp only [F]
    rw [hexp z, gaussianPDFReal_zero_one]
    dsimp [s]
    field_simp [ne_of_gt hσ, ne_of_gt hsqrt,
      ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi))]
    <;> ring
  have hsub := integral_comp_mul_left_Ioi' F (c / s) hs
  have hbound : s * (c / s) = c := by field_simp [ne_of_gt hs]
  rw [hbound] at hsub
  simp only [smul_eq_mul] at hsub
  have hfun : (fun z => F (s * z)) =
      (fun z => s * (z ^ 2 * gaussianPDFReal 0 1 z)) := funext hF
  rw [hfun, integral_const_mul] at hsub
  change 2 * (∫ x in Ioi c, F x) = _
  rw [← hsub]
  dsimp [s]
  ring

end
end SAP.P017.WH.W2.P.T11_L2

theorem SAP.P017.WH.W2.T11_L2_proof : SAP.P017.WH.W2.T11_L2 := by
  intro n hn c σ hc hσ
  have hi := (SAP.P017.WH.W2.P.T11_L2.tail_integrand_integrable n hn σ hσ).integrableOn
    (s := Set.Ioi c)
  constructor
  · simpa only [SAP.P017.wholeTailIntegrand] using hi
  · exact SAP.P017.WH.W2.P.T11_L2.rescale_tail_integral n hn c σ hσ
