import SAP.P004b.WH.W3.Leaves
import AronowAudit.P004.Wave1.DesignLimits.NF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3.P.T27_L8

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology

noncomputable def kernel (t : ℝ) : ℝ := Real.exp (-(t ^ 2 / 2))
noncomputable def normConst : ℝ := (Real.sqrt (2 * Real.pi))⁻¹

lemma kernel_moment_integrable : Integrable (fun t : ℝ => t * kernel t) := by
  have h := integrable_mul_exp_neg_mul_sq (b := (1 : ℝ) / 2) (by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [kernel]
  congr 1
  ring_nf

lemma kernel_first_moment (x : ℝ) :
    ∫ t in Ioi x, t * kernel t = kernel x := by
  have hpow : Tendsto (fun t : ℝ => t ^ 2 / 2) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) (tendsto_pow_atTop (by norm_num))
  have hlim : Tendsto (fun t : ℝ => -kernel t) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hpow)
    simpa [kernel] using h.neg
  have hderiv : ∀ t ∈ Ici x,
      HasDerivAt (fun u : ℝ => -kernel u) (t * kernel t) t := by
    intro t _
    have hp : HasDerivAt (fun u : ℝ => -u ^ 2 / 2) (-t) t := by
      have h := ((hasDerivAt_pow 2 t).neg).div_const 2
      convert h using 1
      norm_num
      ring
    have h := hp.exp.neg
    change HasDerivAt (fun u : ℝ => -kernel u) (t * kernel t) t
    have heq : (fun u : ℝ => -kernel u) =
        -(fun u : ℝ => Real.exp (-u ^ 2 / 2)) := by
      funext u
      dsimp [kernel]
      congr 1
      ring
    rw [heq]
    convert h using 1
    dsimp [kernel]
    norm_num
    ring
  simpa [kernel] using
    (integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
      kernel_moment_integrable.integrableOn hlim)

lemma normal_density_form (t : ℝ) :
    gaussianPDFReal 0 1 t = normConst * kernel t := by
  simp only [gaussianPDFReal, normConst, kernel]
  congr 1
  · congr 1
    norm_num
  · congr 1
    norm_num
    ring

lemma normal_density_nonneg (t : ℝ) : 0 ≤ gaussianPDFReal 0 1 t :=
  gaussianPDFReal_nonneg 0 1 t

lemma sqrt_two_pi_gt_two : 2 < Real.sqrt (2 * Real.pi) := by
  have hpi : 4 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  exact Real.lt_sqrt_of_sq_lt (by nlinarith [hpi] : (2 : ℝ) ^ 2 < 2 * Real.pi)

lemma normal_cdf_zero : normalCDF 0 = 1 / 2 := by
  change (gaussianReal 0 1).real (Iic 0) = 1 / 2
  rw [← cdf_eq_real]
  simpa using AronowAudit.P053.NormalCompletion.normal_cdf_zero

lemma normal_cdf_small_bound (x : ℝ) (hx : 0 ≤ x) :
    normalCDF x ≤ 1 / 2 + x * normConst := by
  let μ : Measure ℝ := gaussianReal 0 1
  have hsplit : μ (Iic x) = μ (Iic 0) + μ (Ioc 0 x) := by
    rw [← measure_union (Iic_disjoint_Ioc (show (0 : ℝ) ≤ 0 by rfl)) measurableSet_Ioc,
      Iic_union_Ioc_eq_Iic hx]
  have hmass : μ.real (Iic x) = μ.real (Iic 0) + μ.real (Ioc 0 x) := by
    rw [measureReal_def, measureReal_def, measureReal_def, hsplit,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hinterval : μ.real (Ioc 0 x) = ∫ t in Ioc 0 x, gaussianPDFReal 0 1 t := by
    rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0)]
    rw [ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Ioc (fun t _ => normal_density_nonneg t)
  have hmax : ∀ t ∈ Ioc 0 x, gaussianPDFReal 0 1 t ≤ normConst := by
    intro t _
    rw [normal_density_form]
    have he : kernel t ≤ 1 := by
      dsimp [kernel]
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (div_nonneg (sq_nonneg t) (by norm_num))
    have hC : 0 ≤ normConst := by dsimp [normConst]; positivity
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he hC
  have hint : (∫ t in Ioc 0 x, gaussianPDFReal 0 1 t) ≤ x * normConst := by
    calc
      (∫ t in Ioc 0 x, gaussianPDFReal 0 1 t) ≤
          ∫ _ in Ioc 0 x, normConst := by
        apply setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
          (integrableOn_const (by simp)) measurableSet_Ioc
        exact hmax
      _ = x * normConst := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hx]
        simp only [smul_eq_mul, sub_zero]
  have hcdf (y : ℝ) : normalCDF y = μ.real (Iic y) := rfl
  have hzero : μ.real (Iic 0) = 1 / 2 := by
    rw [← hcdf 0, normal_cdf_zero]
  rw [hcdf x, hmass, hzero]
  rw [hinterval]
  linarith [hint]

lemma normal_tail_mills (x : ℝ) (hx : 0 < x) :
    (gaussianReal 0 1).real (Ioi x) ≤
      Real.exp (-x ^ 2 / 2) / (x * Real.sqrt (2 * Real.pi)) := by
  let f : ℝ → ℝ := gaussianPDFReal 0 1
  have hpdf : ∀ t, f t = normConst * kernel t := normal_density_form
  have hfint : IntegrableOn f (Ioi x) := (integrable_gaussianPDFReal 0 1).integrableOn
  have hwint : IntegrableOn (fun t : ℝ => (t / x) * f t) (Ioi x) := by
    have hbase := kernel_moment_integrable.const_mul (normConst / x)
    refine hbase.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro t _
    change normConst / x * (t * kernel t) =
      (t / x) * gaussianPDFReal 0 1 t
    rw [normal_density_form t]
    field_simp
  have hcmp : ∀ t ∈ Ioi x, f t ≤ (t / x) * f t := by
    intro t ht
    have ht0 : 0 ≤ f t := normal_density_nonneg t
    have hxt : x ≤ t := ht.le
    have htx : 1 ≤ t / x := by
      apply (le_div_iff₀ hx).2
      simpa using hxt
    calc
      f t = 1 * f t := by ring
      _ ≤ (t / x) * f t := mul_le_mul_of_nonneg_right htx ht0
  have hinter : (∫ t in Ioi x, f t) ≤
      (1 / x) * ∫ t in Ioi x, t * f t := by
    calc
      (∫ t in Ioi x, f t) ≤ ∫ t in Ioi x, (t / x) * f t :=
        setIntegral_mono_on hfint hwint measurableSet_Ioi hcmp
      _ = (1 / x) * ∫ t in Ioi x, t * f t := by
        rw [show (fun t : ℝ => (t / x) * f t) = fun t => (1 / x) * (t * f t) by
          funext t; ring, integral_const_mul]
  have hmoment : ∫ t in Ioi x, t * f t = normConst * kernel x := by
    have heq : (fun t : ℝ => t * f t) = fun t => normConst * (t * kernel t) := by
      funext t
      rw [hpdf t]
      ring
    rw [heq, integral_const_mul, kernel_first_moment]
  have hmeasure : (gaussianReal 0 1).real (Ioi x) = ∫ t in Ioi x, f t := by
    rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0)]
    rw [ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Ioi (fun t _ => normal_density_nonneg t)
  have hxne : x ≠ 0 := ne_of_gt hx
  calc
    (gaussianReal 0 1).real (Ioi x) = ∫ t in Ioi x, f t := hmeasure
    _ ≤ (1 / x) * ∫ t in Ioi x, t * f t := hinter
    _ = Real.exp (-x ^ 2 / 2) / (x * Real.sqrt (2 * Real.pi)) := by
      rw [hmoment]
      dsimp [normConst, kernel]
      field_simp

lemma exp_25_8_gt_eight : (8 : ℝ) < Real.exp (25 / 8) := by
  have h2 : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at h
    exact h
  have hpow : (8 : ℝ) < Real.exp 1 ^ 3 := by
    calc
      (8 : ℝ) = 2 ^ 3 := by norm_num
      _ < Real.exp 1 ^ 3 := by gcongr
  have hthree : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc
    (8 : ℝ) < Real.exp 3 := by rw [hthree]; exact hpow
    _ < Real.exp (25 / 8) := Real.exp_lt_exp.mpr (by norm_num)

end SAP.P004b.WH.W3.P.T27_L8

open SAP.P004b SAP.P004b.WH.W3.P.T27_L8
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology

theorem SAP.P004b.WH.W3.T27_L8_proof : SAP.P004b.WH.W3.T27_L8 := by
  obtain ⟨_, hstrict, _, _, hquant, _, _⟩ :=
    AronowAudit.P004.Wave1.DesignLimits.nf_proof
  have hq : AronowAudit.P004.normalCDF (AronowAudit.P004.normalQuantile (39 / 40)) =
      (39 / 40 : ℝ) :=
    hquant (39 / 40) (by norm_num) (by norm_num)
  have hQuantEq : ∀ a : ℝ,
      SAP.P004b.normalQuantile a = AronowAudit.P004.normalQuantile a := by
    intro a
    rfl
  have hsqrt : 2 < Real.sqrt (2 * Real.pi) := sqrt_two_pi_gt_two
  have hconst : 0 < normConst ∧ normConst < 1 / 2 := by
    constructor
    · dsimp [normConst]
      positivity
    · dsimp [normConst]
      have h := (inv_lt_inv₀ (Real.sqrt_pos.2 (by positivity))
        (by norm_num : (0 : ℝ) < 2)).2 hsqrt
      norm_num at h ⊢
      exact h
  have hlo : normalCDF (5 / 8 : ℝ) < 39 / 40 := by
    have hbound := normal_cdf_small_bound (5 / 8 : ℝ) (by norm_num)
    have hnum : (1 / 2 : ℝ) + (5 / 8) * normConst < 39 / 40 := by
      nlinarith [hconst.2]
    exact lt_of_le_of_lt hbound hnum
  have hCdfEq : ∀ x : ℝ,
      SAP.P004b.normalCDF x = AronowAudit.P004.normalCDF x := by
    intro x
    rfl
  have hquant_lo : (5 / 8 : ℝ) < normalQuantile (39 / 40) := by
    by_contra hn
    have harg : AronowAudit.P004.normalQuantile (39 / 40) ≤ 5 / 8 := by
      simpa only [hQuantEq] using (le_of_not_gt hn)
    have hle := hstrict.monotone harg
    rw [hq] at hle
    have hlo' : AronowAudit.P004.normalCDF (5 / 8 : ℝ) < 39 / 40 := by
      simpa only [hCdfEq] using hlo
    linarith
  have htail : (gaussianReal 0 1).real (Ioi (5 / 2 : ℝ)) < 1 / 40 := by
    have hmills := normal_tail_mills (5 / 2 : ℝ) (by norm_num)
    have hexp : Real.exp (25 / 8) > 8 := exp_25_8_gt_eight
    have hnum : Real.exp (-(5 / 2 : ℝ) ^ 2 / 2) < 1 / 8 := by
      have hrec : (Real.exp (25 / 8))⁻¹ < (8 : ℝ)⁻¹ :=
        by simpa only [one_div] using
          (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 8) hexp)
      have heq : -(5 / 2 : ℝ) ^ 2 / 2 = -(25 / 8 : ℝ) := by norm_num
      rw [heq, Real.exp_neg]
      simpa only [one_div] using hrec
    have hden : (5 / 2 : ℝ) * Real.sqrt (2 * Real.pi) > 5 := by
      nlinarith [hsqrt]
    have hratio : Real.exp (-(5 / 2 : ℝ) ^ 2 / 2) /
        ((5 / 2 : ℝ) * Real.sqrt (2 * Real.pi)) < 1 / 40 := by
      have hD : 0 < (5 / 2 : ℝ) * Real.sqrt (2 * Real.pi) := by positivity
      calc
        _ < (1 / 8 : ℝ) / ((5 / 2 : ℝ) * Real.sqrt (2 * Real.pi)) :=
          div_lt_div_of_pos_right hnum hD
        _ < (1 / 8 : ℝ) / 5 := by
          exact div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 1 / 8)
            (by norm_num : (0 : ℝ) < 5) hden
        _ = 1 / 40 := by norm_num
    exact lt_of_le_of_lt hmills hratio
  have hcomp := measureReal_add_measureReal_compl
    (μ := gaussianReal 0 1) (s := Iic (5 / 2 : ℝ)) measurableSet_Iic
  simp only [compl_Iic, probReal_univ] at hcomp
  have hcdf : normalCDF (5 / 2 : ℝ) =
      (gaussianReal 0 1).real (Iic (5 / 2 : ℝ)) := rfl
  have hhi : 39 / 40 < normalCDF (5 / 2 : ℝ) := by
    rw [hcdf]
    linarith
  have hquant_hi : normalQuantile (39 / 40) < 5 / 2 := by
    by_contra hn
    have harg : (5 / 2 : ℝ) ≤ AronowAudit.P004.normalQuantile (39 / 40) := by
      simpa only [hQuantEq] using (le_of_not_gt hn)
    have hle : AronowAudit.P004.normalCDF (5 / 2) ≤
        AronowAudit.P004.normalCDF (AronowAudit.P004.normalQuantile (39 / 40)) :=
      hstrict.monotone harg
    rw [hq] at hle
    have hhi' : 39 / 40 < AronowAudit.P004.normalCDF (5 / 2 : ℝ) := by
      simpa only [hCdfEq] using hhi
    linarith
  exact ⟨hquant_lo, hquant_hi⟩
