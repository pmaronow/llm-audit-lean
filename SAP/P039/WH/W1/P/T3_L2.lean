import SAP.P039.WH.W1.Leaves
import AronowAudit.P039.P039_StudentCompletion
import AronowAudit.External.StatLean.MultipleTesting.ForMathlib.ChiSquaredInverseMoment
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.WH.W1.P.T3_L2

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

noncomputable section

def mixIntegrand (ν : ℕ) (t w : ℝ) : ℝ :=
  Real.sqrt (w / (ν : ℝ)) *
    ProbabilityTheory.gaussianPDFReal 0 1 (Real.sqrt (w / (ν : ℝ)) * t)

def mixShape (ν : ℕ) : ℝ := (ν : ℝ) / 2

def mixAlpha (ν : ℕ) : ℝ := ((ν : ℝ) + 1) / 2

def mixRate (ν : ℕ) (t : ℝ) : ℝ := (1 + t ^ 2 / (ν : ℝ)) / 2

def mixCoeff (ν : ℕ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (ν : ℝ))⁻¹ *
    ((1 / 2 : ℝ) ^ mixShape ν / Real.Gamma (mixShape ν))

lemma mixIntegrand_mul_gammaPDF (ν : ℕ) (hν : 0 < ν) (t w : ℝ) (hw : 0 < w) :
    mixIntegrand ν t w * gammaPDFReal (mixShape ν) (1 / 2) w =
      mixCoeff ν * (w ^ (mixAlpha ν - 1) * Real.exp (-(mixRate ν t * w))) := by
  have hνr : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast hν
  have hwν : 0 < w / (ν : ℝ) := div_pos hw hνr
  have hs : Real.sqrt (w / (ν : ℝ)) ^ 2 = w / (ν : ℝ) := Real.sq_sqrt hwν.le
  have hνroot : (ν : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (ν : ℝ) :=
    (Real.sqrt_eq_rpow _).symm
  have hcombine : Real.sqrt (w / (ν : ℝ)) * w ^ (mixShape ν - 1) =
      w ^ (mixAlpha ν - 1) / Real.sqrt (ν : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow hw.le hνr.le, hνroot]
    calc
      w ^ (1 / 2 : ℝ) / Real.sqrt (ν : ℝ) * w ^ (mixShape ν - 1) =
          (w ^ (1 / 2 : ℝ) * w ^ (mixShape ν - 1)) / Real.sqrt (ν : ℝ) := by ring
      _ = w ^ (mixAlpha ν - 1) / Real.sqrt (ν : ℝ) := by
        rw [← Real.rpow_add hw]
        congr 1
        dsimp [mixShape, mixAlpha]
        ring
  have hexp :
      Real.exp (-((Real.sqrt (w / (ν : ℝ)) * t) ^ 2) / 2) *
          Real.exp (-((1 / 2 : ℝ) * w)) =
        Real.exp (-(mixRate ν t * w)) := by
    rw [← Real.exp_add, mul_pow, hs]
    dsimp [mixRate]
    congr 1 <;> ring
  rw [mixIntegrand, ProbabilityTheory.gaussianPDFReal]
  simp only [sub_zero, NNReal.coe_one, mul_one]
  rw [ProbabilityTheory.gammaPDFReal, if_pos hw.le]
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          ((1 / 2 : ℝ) ^ mixShape ν / Real.Gamma (mixShape ν)) *
          (Real.sqrt (w / (ν : ℝ)) * w ^ (mixShape ν - 1)) *
          (Real.exp (-((Real.sqrt (w / (ν : ℝ)) * t) ^ 2) / 2) *
            Real.exp (-((1 / 2 : ℝ) * w))) := by ring
    _ = mixCoeff ν * (w ^ (mixAlpha ν - 1) *
          Real.exp (-(mixRate ν t * w))) := by
      rw [hcombine, hexp]
      dsimp [mixCoeff]
      ring

lemma mix_integral_real (ν : ℕ) (hν : 0 < ν) (t : ℝ) :
    (∫ w : ℝ, mixIntegrand ν t w ∂gammaMeasure (mixShape ν) (1 / 2)) =
      Real.Gamma (mixAlpha ν) /
        (Real.sqrt ((ν : ℝ) * Real.pi) * Real.Gamma (mixShape ν)) *
          (1 + t ^ 2 / (ν : ℝ)) ^ (-mixAlpha ν) := by
  have hνr : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast hν
  have ha : 0 < mixShape ν := by dsimp [mixShape]; linarith
  have hr : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  have hα : 0 < mixAlpha ν := by dsimp [mixAlpha]; positivity
  have hc : 0 < mixRate ν t := by
    dsimp [mixRate]
    positivity
  rw [AronowAudit.GaussianCompletion.integral_gamma_eq_setIntegral ha hr]
  have hcongr :
      (∫ w : ℝ in Ioi 0,
        gammaPDFReal (mixShape ν) (1 / 2) w * mixIntegrand ν t w) =
      ∫ w : ℝ in Ioi 0,
        mixCoeff ν * (w ^ (mixAlpha ν - 1) * Real.exp (-(mixRate ν t * w))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w hw
    simpa [mul_comm] using mixIntegrand_mul_gammaPDF ν hν t w hw
  rw [hcongr]
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hα hc]
  have hrate :
      (1 / mixRate ν t) ^ mixAlpha ν =
        (2 : ℝ) ^ mixAlpha ν * (1 + t ^ 2 / (ν : ℝ)) ^ (-mixAlpha ν) := by
    have hx : 0 < 1 + t ^ 2 / (ν : ℝ) := by positivity
    have heq : 1 / mixRate ν t = 2 / (1 + t ^ 2 / (ν : ℝ)) := by
      dsimp [mixRate]
      field_simp
    rw [heq, Real.div_rpow (by norm_num) hx.le, div_eq_mul_inv,
      Real.rpow_neg hx.le]
  have htwo :
      (1 / 2 : ℝ) ^ mixShape ν * (2 : ℝ) ^ mixAlpha ν = Real.sqrt 2 := by
    have hsum : -mixShape ν + mixAlpha ν = (1 / 2 : ℝ) := by
      dsimp [mixShape, mixAlpha]
      ring
    calc
      (1 / 2 : ℝ) ^ mixShape ν * (2 : ℝ) ^ mixAlpha ν
          = (2 : ℝ) ^ (-mixShape ν + mixAlpha ν) := by
              rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num]
              rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
              congr 1 <;> ring
      _ = Real.sqrt 2 := by rw [hsum, Real.sqrt_eq_rpow]
  have hconst :
      mixCoeff ν * ((2 : ℝ) ^ mixAlpha ν) =
        1 / (Real.sqrt ((ν : ℝ) * Real.pi) * Real.Gamma (mixShape ν)) := by
    have hprod :
        ((1 / 2 : ℝ) ^ mixShape ν / Real.Gamma (mixShape ν)) *
            (2 : ℝ) ^ mixAlpha ν = Real.sqrt 2 / Real.Gamma (mixShape ν) := by
      calc
        _ = ((1 / 2 : ℝ) ^ mixShape ν * (2 : ℝ) ^ mixAlpha ν) /
              Real.Gamma (mixShape ν) := by ring
        _ = _ := by rw [htwo]
    have h2π : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
      Real.sqrt_mul (x := (2 : ℝ)) (by positivity) Real.pi
    have hνπ : Real.sqrt (ν : ℝ) * Real.sqrt Real.pi =
        Real.sqrt ((ν : ℝ) * Real.pi) := by
      rw [← Real.sqrt_mul (x := (ν : ℝ)) (by positivity) Real.pi]
    dsimp [mixCoeff]
    calc
      _ = (Real.sqrt (2 * Real.pi))⁻¹ *
            (Real.sqrt (ν : ℝ))⁻¹ *
              (Real.sqrt 2 / Real.Gamma (mixShape ν)) := by
          calc
            _ = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (ν : ℝ))⁻¹ *
                  (((1 / 2 : ℝ) ^ mixShape ν / Real.Gamma (mixShape ν)) *
                    (2 : ℝ) ^ mixAlpha ν) := by ring
            _ = _ := by rw [hprod]
      _ = 1 / (Real.sqrt ((ν : ℝ) * Real.pi) *
            Real.Gamma (mixShape ν)) := by
          rw [h2π, ← hνπ]
          field_simp <;> ring
  rw [hrate]
  calc
    mixCoeff ν * ((2 : ℝ) ^ mixAlpha ν *
        (1 + t ^ 2 / (ν : ℝ)) ^ (-mixAlpha ν) * Real.Gamma (mixAlpha ν)) =
        (mixCoeff ν * (2 : ℝ) ^ mixAlpha ν) * Real.Gamma (mixAlpha ν) *
          (1 + t ^ 2 / (ν : ℝ)) ^ (-mixAlpha ν) := by ring
    _ = _ := by rw [hconst]; ring

end
end SAP.P039.WH.W1.P.T3_L2

open SAP.P039.WH.W1.P.T3_L2 ProbabilityTheory MeasureTheory
open scoped ENNReal

theorem SAP.P039.WH.W1.T3_L2_proof : SAP.P039.WH.W1.T3_L2 := by
  intro ν hν t
  have hνr : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast hν
  have ha : 0 < mixShape ν := by dsimp [mixShape]; linarith
  have hr : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  let μ := gammaMeasure (mixShape ν) (1 / 2 : ℝ)
  let f := mixIntegrand ν t
  have hfnon : 0 ≤ᵐ[μ] f := ae_of_all _ (fun w => by
    dsimp [f, mixIntegrand]
    exact mul_nonneg (Real.sqrt_nonneg _) (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _))
  have hfm : AEStronglyMeasurable f μ := by
    have hm : Measurable (mixIntegrand ν t) := by
      unfold mixIntegrand
      fun_prop
    exact hm.aestronglyMeasurable
  let L : ℝ≥0∞ := ∫⁻ w : ℝ, ENNReal.ofReal (f w) ∂μ
  have hlin : (∫ w : ℝ, f w ∂μ) = ENNReal.toReal L := by
    exact integral_eq_lintegral_of_nonneg_ae hfnon hfm
  have hival := mix_integral_real ν hν t
  have hpos : 0 < ENNReal.toReal L := by
    rw [← hlin, hival]
    apply mul_pos
    · apply div_pos
      · exact Real.Gamma_pos_of_pos (by dsimp [mixAlpha]; positivity)
      · apply mul_pos
        · exact Real.sqrt_pos.2 (mul_pos hνr Real.pi_pos)
        · exact Real.Gamma_pos_of_pos ha
    · exact Real.rpow_pos_of_pos (by positivity) _
  have htop : L ≠ ⊤ := (ENNReal.toReal_ne_zero.mp (ne_of_gt hpos)).2
  have hconv : ENNReal.ofReal (∫ w : ℝ, f w ∂μ) = L := by
    rw [hlin]
    exact ENNReal.ofReal_toReal htop
  change (∫⁻ w : ℝ, ENNReal.ofReal
      (Real.sqrt (w / (ν : ℝ)) * gaussianPDFReal 0 1
        (Real.sqrt (w / (ν : ℝ)) * t)) ∂gammaMeasure ((ν : ℝ) / 2) (1 / 2)) = _
  change L = _
  rw [← hconv, hival]
  rw [wholeStudentDensity]
  dsimp [mixShape, mixAlpha]
