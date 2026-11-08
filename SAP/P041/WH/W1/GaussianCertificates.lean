import SAP.P041.WH.W1.Helpers

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W1
open MeasureTheory ProbabilityTheory
open AronowAudit.P041.Wave1

/-- The donor quantile is a genuine positive critical point at every
nondegenerate significance level; in particular its infimum is well defined. -/
theorem normal_critical_exists (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    NormalCriticalW1 α (AronowAudit.P053.normalCritical α) := by
  let c := AronowAudit.P053.normalCritical α
  have hc : 0 < c := AronowAudit.P053.NormalCompletion.normalCritical_pos α hα hα1
  have he : normalTwoSided c = α := by
    have hcdf := AronowAudit.P053.NormalCompletion.normalCritical_cdf α hα hα1
    rw [AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf] at hcdf
    unfold normalTwoSided
    rw [abs_of_pos hc, AronowAudit.P053.NormalCompletion.normal_cdf_neg]
    change 2*(1-ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) c) = α
    linarith
  refine ⟨hc,he,?_⟩
  intro d hd heD
  apply neg_injective
  apply AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.injective
  unfold normalTwoSided at he heD
  rw [abs_of_pos hc] at he
  rw [abs_of_nonneg hd] at heD
  linarith

/-- The sharper normalizer needed by the seven- and nine-decimal leaves. -/
theorem normal_density_fine :
    (0.39894228040143267 : ℝ) ≤ 1/Real.sqrt (2*Real.pi) ∧
    1/Real.sqrt (2*Real.pi) ≤ 0.39894228040143269 := by
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  constructor
  · apply (le_div_iff₀ hs).mpr
    nlinarith [Real.pi_lt_d20, sq_nonneg (0.39894228040143267*Real.sqrt (2*Real.pi)-1)]
  · apply (div_le_iff₀ hs).mpr
    nlinarith [Real.pi_gt_d20, sq_nonneg (0.39894228040143269*Real.sqrt (2*Real.pi)-1)]

/-- A reusable sharp finite Gaussian certificate; all integrals are of a
continuous function over a finite interval. -/
theorem normal_tail_fine (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hp : 0 ≤ normal_intPoly (2*n+1) x) :
    1 - 2*0.39894228040143269*normal_intPoly (2*n) x ≤
      2*cdf (gaussianReal 0 1) (-x) ∧
    2*cdf (gaussianReal 0 1) (-x) ≤
      1 - 2*0.39894228040143267*normal_intPoly (2*n+1) x := by
  obtain ⟨hl,hu⟩ := normal_integral_bracket n x hx
  obtain ⟨hc0,hc1⟩ := normal_density_fine
  have hi : 0 ≤ ∫ t in 0..x, Real.exp (-(t^2/2)) :=
    intervalIntegral.integral_nonneg hx (fun t _ => (Real.exp_pos _).le)
  have hcoef : 0 ≤ 1/Real.sqrt (2*Real.pi) := by positivity
  rw [normal_cdf_integral x hx]
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hu hcoef
    have h2 := mul_le_mul_of_nonneg_right hc1 (le_trans hi hu)
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hl hcoef
    have h2 := mul_le_mul_of_nonneg_right hc0 hp
    nlinarith

end SAP.P041.WH.W1
