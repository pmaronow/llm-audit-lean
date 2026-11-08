import SAP.P039.WH.W1.Leaves
import AronowAudit.External.StatLean.MultipleTesting.ForMathlib.ChiSquaredInverseMoment
import AronowAudit.P039.P039_StudentCompletion
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.WH.W1.P.T7_L1

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

theorem integrable_inv_sq_gamma {a r : ℝ} (ha : 2 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ => (x⁻¹) ^ 2) (gammaMeasure a r) := by
  have ha0 : 0 < a := by linarith
  have hpdf : Measurable (gammaPDF a r) :=
    (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, integrable_withDensity_iff hpdf
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have he : (fun x : ℝ => (x⁻¹) ^ 2 * (gammaPDF a r x).toReal) =
      fun x => gammaPDFReal a r x * (x⁻¹) ^ 2 := by
    funext x
    rw [show gammaPDF a r x = ENNReal.ofReal (gammaPDFReal a r x) from rfl,
      ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha0 hr x)]
    ring
  rw [he]
  have hm : IntegrableOn
      (fun x : ℝ => x ^ (a - 3) * Real.exp (-(r * x))) (Ioi 0) := by
    have hh := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 3) (b := r)
      (by linarith) (by norm_num) hr
    exact hh.congr_fun (fun x hx => by simp only [Real.rpow_one, neg_mul]) measurableSet_Ioi
  have hmc : IntegrableOn
      (fun x : ℝ => r ^ a / Real.Gamma a *
        (x ^ (a - 3) * Real.exp (-(r * x)))) (Ioi 0) := hm.const_mul _
  have hm' : IntegrableOn (fun x : ℝ => gammaPDFReal a r x * (x⁻¹) ^ 2) (Ioi 0) := by
    refine hmc.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hpow : (x⁻¹) ^ 2 = x ^ (-2 : ℝ) := by
      calc
        (x⁻¹) ^ 2 = (x ^ 2)⁻¹ := by rw [inv_pow]
        _ = x ^ (-2 : ℝ) := by
          rw [← Real.rpow_natCast x 2]
          exact (Real.rpow_neg hx.le (2 : ℝ)).symm
    rw [hpow]
    have hg := (AronowAudit.P039.StudentCompletion.gamma_rpow_integrand
      (a := a) (r := r) (q := -2) x hx).symm
    rw [show a + (-2 : ℝ) - 1 = a - 3 by ring] at hg
    simpa [mul_assoc] using hg
  have hz : (fun x : ℝ => gammaPDFReal a r x * (x⁻¹) ^ 2) =
      (Ioi (0 : ℝ)).indicator (fun x => gammaPDFReal a r x * (x⁻¹) ^ 2) := by
    funext x
    by_cases hx : 0 < x
    · simp [hx]
    · have hxn : x ≤ 0 := le_of_not_gt hx
      have hp : gammaPDFReal a r x = 0 := by
        by_cases hn : x < 0
        · simp [gammaPDFReal, hn]
        · have h0 : x = 0 := le_antisymm hxn (le_of_not_gt hn)
          subst x
          simp [gammaPDFReal, Real.zero_rpow, ne_of_gt (by linarith : 0 < a - 1)]
      simp [mem_Ioi, hx, hp]
  rw [hz]
  exact (integrable_indicator_iff measurableSet_Ioi).mpr hm'

theorem integral_inv_sq_gamma {a r : ℝ} (ha : 2 < a) (hr : 0 < r) :
    (∫ x : ℝ, (x⁻¹) ^ 2 ∂gammaMeasure a r) =
      r ^ 2 / ((a - 1) * (a - 2)) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a - 2 := by linarith
  have hintegrand : ∀ x ∈ Ioi (0 : ℝ),
      gammaPDFReal a r x * (x⁻¹) ^ 2 =
        r ^ a / Real.Gamma a * (x ^ (a - 3) * Real.exp (-(r * x))) := by
    intro x hx
    have hpow : (x⁻¹) ^ 2 = x ^ (-2 : ℝ) := by
      calc
        (x⁻¹) ^ 2 = (x ^ 2)⁻¹ := by rw [inv_pow]
        _ = x ^ (-2 : ℝ) := by
          rw [← Real.rpow_natCast x 2]
          exact (Real.rpow_neg hx.le (2 : ℝ)).symm
    rw [hpow]
    have hg := AronowAudit.P039.StudentCompletion.gamma_rpow_integrand
      (a := a) (r := r) (q := -2) x hx
    rw [show a + (-2 : ℝ) - 1 = a - 3 by ring] at hg
    simpa [mul_assoc] using hg
  rw [AronowAudit.GaussianCompletion.integral_gamma_eq_setIntegral ha0 hr]
  rw [setIntegral_congr_fun measurableSet_Ioi hintegrand]
  rw [integral_const_mul]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha1 hr
  have h' : a - 3 = (a - 2) - 1 := by ring
  have hI : (∫ t : ℝ in Ioi 0, t ^ (a - 3) * Real.exp (-(r * t))) =
      (1 / r) ^ (a - 2) * Real.Gamma (a - 2) := by
    simpa only [← h'] using h
  rw [hI]
  have hG1 : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    calc
      Real.Gamma a = Real.Gamma ((a - 1) + 1) := by congr 1 <;> ring
      _ = (a - 1) * Real.Gamma (a - 1) :=
        Real.Gamma_add_one (by linarith : a - 1 ≠ 0)
  have hG2 : Real.Gamma (a - 1) = (a - 2) * Real.Gamma (a - 2) := by
    calc
      Real.Gamma (a - 1) = Real.Gamma ((a - 2) + 1) := by congr 1 <;> ring
      _ = (a - 2) * Real.Gamma (a - 2) :=
        Real.Gamma_add_one (by linarith : a - 2 ≠ 0)
  rw [hG1, hG2]
  have hrpow : r ^ a = r ^ (a - 2) * r ^ 2 := by
    calc
      r ^ a = r ^ ((a - 2) + 2) := by congr 1 <;> ring
      _ = r ^ (a - 2) * r ^ 2 := by
        rw [Real.rpow_add hr]
        exact congrArg (fun y : ℝ => r ^ (a - 2) * y) (Real.rpow_natCast r 2)
  rw [hrpow]
  rw [show (1 / r) ^ (a - 2) = (r ^ (a - 2))⁻¹ by
    rw [one_div, Real.inv_rpow hr.le]]
  have hpowpos : r ^ (a - 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hr (a - 2))
  have hgampos : Real.Gamma (a - 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos ha1)
  field_simp [hpowpos, hgampos]

end SAP.P039.WH.W1.P.T7_L1

open SAP.P039.WH.W1.P.T7_L1
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

theorem SAP.P039.WH.W1.T7_L1_proof : SAP.P039.WH.W1.T7_L1 := by
  intro ν hν
  have hνpos : 0 < ν := by omega
  have hshape : 2 < (ν : ℝ) / 2 := by
    have hn : (4 : ℝ) < ν := by exact_mod_cast hν
    linarith
  have hmap : SAP.P039.chiSquaredLaw ν =
      gammaMeasure ((ν : ℝ) / 2) (1 / 2) := by
    change (Measure.pi (fun _ : Fin ν => gaussianReal 0 1)).map
      (fun z => ∑ i, (z i) ^ 2) = _
    exact AronowAudit.GaussianCompletion.gaussian_squares_eq_gamma hνpos
  constructor
  · rw [hmap]
    exact integrable_inv_sq_gamma hshape (by norm_num)
  · rw [hmap]
    rw [integral_inv_sq_gamma hshape (by norm_num)]
    have hn : (4 : ℝ) < ν := by exact_mod_cast hν
    have h1 : (ν : ℝ) / 2 - 1 ≠ 0 := by linarith
    have h2 : (ν : ℝ) / 2 - 2 ≠ 0 := by linarith
    field_simp [h1, h2]
  <;> ring
