import AronowAudit.P010.P010_Population
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Probability.Distributions.Exponential

/-!
P010-T3: the missing passing-condition counterexample.

The exponential and Laplace calculations are proved from their densities and
Mathlib's Gamma integral. Product-law calculations then give the exact potential
pair/assignment laws, the observed law and the all-pass law. The final calculation
compares the printed tail means with the always-passer means and restores the
passing condition for the corrected bounds.
-/

namespace AronowAudit.P010.Wave1

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical

noncomputable section

/-- The positive exponential component, with the null endpoint omitted. -/
def missing_pass_exp (r : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (if 0 < x then r * Real.exp (-(r*x)) else 0))

lemma missing_pass_exp_eq (r : ℝ) : missing_pass_exp r = expMeasure r := by
  unfold missing_pass_exp expMeasure gammaMeasure
  apply withDensity_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
  change ENNReal.ofReal _ = exponentialPDF r x
  rw [exponentialPDF_eq]
  by_cases h : 0 < x
  · simp [h, h.le]
  · simp [h, show ¬ 0 ≤ x by grind]

lemma missing_pass_exp_prob (r : ℝ) (hr : 0 < r) :
    IsProbabilityMeasure (missing_pass_exp r) := by
  rw [missing_pass_exp_eq]
  exact isProbabilityMeasure_expMeasure hr

lemma missing_pass_exp_one : missing_pass_exp 1 = exponentialOne := by
  simp [missing_pass_exp, exponentialOne]

lemma missing_pass_exp_density_measurable (r : ℝ) :
    Measurable (fun x : ℝ => ENNReal.ofReal (if 0 < x then r * Real.exp (-(r*x)) else 0)) := by
  exact (Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (by fun_prop) measurable_const).ennreal_ofReal

lemma missing_pass_exp_integral (r : ℝ) (hr : 0 < r) (f : ℝ → ℝ) :
    (∫ x, f x ∂missing_pass_exp r) =
      r * ∫ x in Ioi 0, Real.exp (-(r*x)) * f x := by
  unfold missing_pass_exp
  rw [integral_withDensity_eq_integral_toReal_smul
    (missing_pass_exp_density_measurable r)
    (by filter_upwards [] with x; exact ENNReal.ofReal_lt_top)]
  rw [← integral_const_mul, ← integral_indicator measurableSet_Ioi]
  congr 1
  ext x
  by_cases hx : 0 < x
  · simp [hx, ENNReal.toReal_ofReal (mul_nonneg hr.le (Real.exp_pos _).le), mul_assoc]
  · simp [hx]

lemma missing_pass_exp_integrable (r : ℝ) (hr : 0 < r) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun x => Real.exp (-(r*x))*f x) (Ioi 0)) :
    Integrable f (missing_pass_exp r) := by
  unfold missing_pass_exp
  rw [integrable_withDensity_iff (missing_pass_exp_density_measurable r)
    (by filter_upwards [] with x; exact ENNReal.ofReal_lt_top)]
  have hi := (integrable_indicator_iff measurableSet_Ioi).mpr (hf.const_mul r)
  apply hi.congr
  filter_upwards [] with x
  by_cases hx : 0 < x
  · simp [hx, ENNReal.toReal_ofReal (mul_nonneg hr.le (Real.exp_pos _).le),
      mul_comm, mul_left_comm, mul_assoc]
  · simp [hx]

lemma missing_pass_gamma_integrable (r : ℝ) (hr : 0 < r) (n : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(r*x))*x^n) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => Real.exp (-x)*x^n) (Ioi 0) := by
    convert Real.GammaIntegral_convergent (s := (n:ℝ)+1) (by positivity) using 1
    simp
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ => Real.exp (-x)*x^n) 0 hr).mpr (by simpa using hg)
  have hi := hs.const_mul (r^n)⁻¹
  apply hi.congr
  filter_upwards [] with x
  rw [mul_pow]
  field_simp

lemma missing_pass_exp_moment (r : ℝ) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x : ℝ => |x|^n) (missing_pass_exp r) ∧
    (∫ x : ℝ, x^n ∂missing_pass_exp r) = (n.factorial : ℝ) / r^n := by
  constructor
  · apply missing_pass_exp_integrable r hr
    apply (missing_pass_gamma_integrable r hr n).congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    simp [abs_of_pos (show 0 < x from hx)]
  · rw [missing_pass_exp_integral r hr]
    have hv := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (n:ℝ)+1) (by positivity) hr
    simp only [add_sub_cancel_right, Real.rpow_natCast,
      Real.Gamma_nat_eq_factorial] at hv
    rw [show (fun x : ℝ => Real.exp (-(r*x))*x^n) =
      (fun x : ℝ => x^n*Real.exp (-(r*x))) from funext (fun _ => mul_comm _ _),
      hv, Real.rpow_add_one (by positivity : (1/r:ℝ) ≠ 0), Real.rpow_natCast]
    field_simp [hr.ne']
    rw [← mul_pow]
    simp [hr.ne']

lemma missing_pass_neg_density (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (volume.withDensity f).map (fun x => -x) =
      volume.withDensity (fun x => f (-x)) := by
  ext s hs
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs]
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
    hs (hf.comp measurable_neg)
  simpa only [Function.comp_def, neg_neg] using h

lemma missing_pass_laplace_split (r : ℝ) (hr : 0 < r) :
    laplaceRate r = (1/2 : ℝ≥0∞) • missing_pass_exp r +
      (1/2 : ℝ≥0∞) • (missing_pass_exp r).map (fun x => -x) := by
  unfold laplaceRate missing_pass_exp
  rw [missing_pass_neg_density _ (missing_pass_exp_density_measurable r),
    ← withDensity_smul' (1/2) _ (by norm_num),
    ← withDensity_smul' (1/2) _ (by norm_num),
    ← withDensity_add_left ((missing_pass_exp_density_measurable r).const_smul (1/2 : ℝ≥0∞))]
  apply withDensity_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
  have hh : (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hh]
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  by_cases hp : 0 < x
  · simp only [ite_eq_left hp, ite_eq_right (show ¬ 0 < -x by linarith), abs_of_pos hp,
      mul_zero, ENNReal.ofReal_zero, add_zero]
    congr 1
    ring_nf
  · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    simp only [ite_eq_right hp, ite_eq_left (neg_pos.mpr hn), abs_of_neg hn,
      mul_zero, ENNReal.ofReal_zero, zero_add]
    congr 1
    ring_nf

lemma missing_pass_laplace_prob (r : ℝ) (hr : 0 < r) :
    IsProbabilityMeasure (laplaceRate r) := by
  letI := missing_pass_exp_prob r hr
  constructor
  rw [missing_pass_laplace_split r hr]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  simpa only [one_div] using ENNReal.inv_two_add_inv_two

lemma missing_pass_laplace_moments (r : ℝ) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x : ℝ => |x|^n) (laplaceRate r) := by
  have hi := (missing_pass_exp_moment r hr n).1
  rw [missing_pass_laplace_split r hr, integrable_add_measure]
  refine ⟨hi.smul_measure (by norm_num), ?_⟩
  apply Integrable.smul_measure _ (by norm_num)
  rw [integrable_map_measure (by fun_prop) measurable_neg.aemeasurable]
  simpa only [Function.comp_def, abs_neg] using hi

lemma missing_pass_laplace_atomless (r : ℝ) : Atomless (laplaceRate r) := by
  intro x
  unfold laplaceRate
  exact measure_singleton x

lemma missing_pass_exp_pos (r : ℝ) (hr : 0 < r) :
    ∀ᵐ x ∂missing_pass_exp r, 0 < x := by
  letI := missing_pass_exp_prob r hr
  letI := isProbabilityMeasure_expMeasure hr
  have hz : (missing_pass_exp r (Iic 0)).toReal = 0 := by
    rw [missing_pass_exp_eq]
    change (expMeasure r).real (Iic 0) = 0
    rw [← cdf_eq_real, cdf_expMeasure_eq hr]
    norm_num
  have hm : missing_pass_exp r (Iic 0) = 0 := by
    exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top _ _)
  rw [ae_iff]
  simpa only [not_lt, Iic] using hm

lemma missing_pass_integrable_id {μ : Measure ℝ}
    (h : Integrable (fun x : ℝ => |x|^1) μ) : Integrable (fun x : ℝ => x) μ := by
  apply (integrable_norm_iff measurable_id'.aestronglyMeasurable).mp
  simpa using h

lemma missing_pass_exp_mean (r : ℝ) (hr : 0 < r) :
    (∫ x : ℝ, x ∂missing_pass_exp r) = 1/r := by
  simpa using (missing_pass_exp_moment r hr 1).2

lemma missing_pass_exp_halves (r : ℝ) (hr : 0 < r) :
    missing_pass_exp r (Iic 0) = 0 ∧ missing_pass_exp r (Ici 0) = 1 ∧
    (∫ x : ℝ in Iic 0, x ∂missing_pass_exp r) = 0 ∧
    (∫ x : ℝ in Ici 0, x ∂missing_pass_exp r) = 1/r := by
  letI := missing_pass_exp_prob r hr
  have hp := missing_pass_exp_pos r hr
  have h0 : Iic (0:ℝ) =ᵐ[missing_pass_exp r] (∅ : Set ℝ) := by
    filter_upwards [hp] with x hx
    simp [show ¬ x ≤ 0 by linarith]
  have h1 : Ici (0:ℝ) =ᵐ[missing_pass_exp r] (univ : Set ℝ) := by
    filter_upwards [hp] with x hx
    simp [hx.le]
  rw [measure_congr h0, measure_congr h1, setIntegral_congr_set h0,
    setIntegral_congr_set h1]
  simp [missing_pass_exp_mean r hr]

lemma missing_pass_laplace_halves (r : ℝ) (hr : 0 < r) :
    laplaceRate r (Iic 0) = 1/2 ∧ laplaceRate r (Ici 0) = 1/2 ∧
    (∫ x : ℝ in Iic 0, x ∂laplaceRate r) = -(1/(2*r)) ∧
    (∫ x : ℝ in Ici 0, x ∂laplaceRate r) = 1/(2*r) := by
  have he := missing_pass_exp_halves r hr
  have hi := missing_pass_integrable_id (missing_pass_exp_moment r hr 1).1
  have hn : Integrable (fun x : ℝ => x) ((missing_pass_exp r).map (fun x => -x)) := by
    rw [integrable_map_measure measurable_id'.aestronglyMeasurable measurable_neg.aemeasurable]
    exact hi.neg
  have pre0 : (fun x : ℝ => -x) ⁻¹' Iic 0 = Ici 0 := by ext x; simp
  have pre1 : (fun x : ℝ => -x) ⁻¹' Ici 0 = Iic 0 := by ext x; simp
  have hv0 : (∫ x : ℝ in Iic 0, x ∂(missing_pass_exp r).map (fun x => -x)) = -(1/r) := by
    rw [setIntegral_map measurableSet_Iic measurable_id'.aestronglyMeasurable
      measurable_neg.aemeasurable, pre0, integral_neg, he.2.2.2]
  have hv1 : (∫ x : ℝ in Ici 0, x ∂(missing_pass_exp r).map (fun x => -x)) = 0 := by
    rw [setIntegral_map measurableSet_Ici measurable_id'.aestronglyMeasurable
      measurable_neg.aemeasurable, pre1, integral_neg, he.2.2.1, neg_zero]
  rw [missing_pass_laplace_split r hr]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_neg measurableSet_Iic,
    Measure.map_apply measurable_neg measurableSet_Ici, pre0, pre1, he.1, he.2.1,
    mul_zero, mul_one, zero_add, add_zero]
  refine ⟨True.intro, True.intro, ?_, ?_⟩
  · rw [Measure.restrict_add, integral_add_measure
      ((hi.smul_measure (by norm_num : (1/2:ℝ≥0∞) ≠ ∞)).integrableOn)
      ((hn.smul_measure (by norm_num : (1/2:ℝ≥0∞) ≠ ∞)).integrableOn)]
    simp [Measure.restrict_smul, integral_smul_measure, he.2.2.1, hv0,
      ENNReal.toReal_div, ENNReal.toReal_ofNat]
    ring_nf
  · rw [Measure.restrict_add, integral_add_measure
      ((hi.smul_measure (by norm_num : (1/2:ℝ≥0∞) ≠ ∞)).integrableOn)
      ((hn.smul_measure (by norm_num : (1/2:ℝ≥0∞) ≠ ∞)).integrableOn)]
    simp [Measure.restrict_smul, integral_smul_measure, he.2.2.2, hv1,
      ENNReal.toReal_div, ENNReal.toReal_ofNat]
    ring_nf

lemma missing_pass_laplace_support (r : ℝ) (hr : 0 < r) (l u : ℝ) (hlu : l < u) :
    0 < laplaceRate r (Ioo l u) := by
  have hac : volume ≪ laplaceRate r := by
    apply withDensity_absolutelyContinuous' (by fun_prop)
    filter_upwards [] with x
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos (by positivity) (Real.exp_pos _)))
  apply pos_iff_ne_zero.mpr
  intro hz
  have hv := hac hz
  have : 0 < volume (Ioo l u) := by simpa using ENNReal.ofReal_pos.mpr (sub_pos.mpr hlu)
  exact (ne_of_gt this) hv

lemma missing_pass_laplace_median : quantile (laplaceRate 1) (1/2) = 0 := by
  letI := missing_pass_laplace_prob 1 (by norm_num)
  have hh := (missing_pass_laplace_halves 1 (by norm_num)).1
  have hlt (x : ℝ) (hx : x < 0) : (laplaceRate 1 (Iic x)).toReal < 1/2 := by
    have hpos : 0 < (laplaceRate 1).real (Iic 0 \ Iic x) := by
      have hp := ENNReal.toReal_pos (ne_of_gt (missing_pass_laplace_support 1
        (by norm_num) x 0 hx)) (measure_ne_top (laplaceRate 1) (Ioo x 0))
      exact lt_of_lt_of_le hp (measureReal_mono (by
        intro y hy
        exact ⟨hy.2.le, not_le.mpr hy.1⟩))
    rw [measureReal_sdiff (Iic_subset_Iic.mpr hx.le) measurableSet_Iic] at hpos
    simpa [measureReal_def, hh] using hpos
  unfold quantile
  apply le_antisymm
  · apply sInf_le
    change 1/2 ≤ (laplaceRate 1 {y : ℝ | (y:EReal) ≤ 0}).toReal
    simp only [← EReal.coe_zero, EReal.coe_le_coe_iff]
    change 1/2 ≤ (laplaceRate 1 (Iic 0)).toReal
    rw [hh]
    norm_num
  · apply le_sInf
    intro q hq
    by_contra hn
    have hq0 : q < 0 := lt_of_not_ge hn
    cases q using EReal.rec with
    | bot => norm_num at hq
    | top => simp at hq0
    | coe x =>
      have hx : x < 0 := by exact_mod_cast hq0
      have hm := hlt x hx
      simp only [mem_ofPred_eq, EReal.coe_le_coe_iff] at hq
      change (1/2 : ℝ) ≤ (laplaceRate 1 (Iic x)).toReal at hq
      linarith

local instance missing_pass_expOne_prob : IsProbabilityMeasure exponentialOne := by
  rw [← missing_pass_exp_one]
  exact missing_pass_exp_prob 1 (by norm_num)

local instance missing_pass_laplaceOne_prob : IsProbabilityMeasure (laplaceRate 1) :=
  missing_pass_laplace_prob 1 (by norm_num)

local instance missing_pass_laplaceTwo_prob : IsProbabilityMeasure (laplaceRate 2) :=
  missing_pass_laplace_prob 2 (by norm_num)

local instance missing_pass_fair_prob : IsProbabilityMeasure fairAssignment := by
  constructor
  simp only [fairAssignment, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  simpa only [one_div] using ENNReal.inv_two_add_inv_two

local instance missing_pass_stratum_prob (s t : Bool) (F G : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G] : IsProbabilityMeasure (stratumLaw s t F G) := by
  unfold stratumLaw
  infer_instance

lemma missing_pass_prob (upper : Bool) : IsProbabilityMeasure (missingPassLaw upper) := by
  cases upper <;> constructor <;>
    simp only [missingPassLaw, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
      Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] <;>
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp <;>
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]

lemma missing_pass_stratum_joint (s t : Bool) (F G : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G] (a : Fin 2) :
    (stratumLaw s t F G).map
      (fun ω => ((potentialY a ω, potentialS a ω), assignment ω)) =
    (if a = 0 then F.map (fun x => (x,s)) else G.map (fun x => (x,t))).prod fairAssignment := by
  unfold stratumLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  fin_cases a
  · simp only [↓reduceIte]
    change (((F.prod G).prod fairAssignment).map
      (Prod.map (fun p : ℝ × ℝ => (p.1,s)) id)) = _
    rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id]
    have hm : (F.prod G).map (fun p : ℝ × ℝ => (p.1,s)) = F.map (fun x => (x,s)) := by
      change (F.prod G).map ((fun x : ℝ => (x,s)) ∘ Prod.fst) = _
      rw [← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod,
        measure_univ, one_smul]
    rw [hm]
    simp [Fin.ext_iff]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.reduceEq, ↓reduceIte]
    change (((F.prod G).prod fairAssignment).map
      (Prod.map (fun p : ℝ × ℝ => (p.2,t)) id)) = _
    rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id]
    have hm : (F.prod G).map (fun p : ℝ × ℝ => (p.2,t)) = G.map (fun x => (x,t)) := by
      change (F.prod G).map ((fun x : ℝ => (x,t)) ∘ Prod.snd) = _
      rw [← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod,
        measure_univ, one_smul]
    rw [hm]
    simp [Fin.ext_iff]

lemma missing_pass_half_sq : (1/2:ℝ≥0∞)*(1/2) = 1/4 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

lemma missing_pass_quarter_half : (1/4:ℝ≥0∞) + 1/2 = 3/4 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]

def missing_pass_signed (upper : Bool) : Measure ℝ :=
  if upper then exponentialOne else exponentialOne.map (fun x => -x)

local instance missing_pass_signed_prob (u : Bool) : IsProbabilityMeasure (missing_pass_signed u) := by
  cases u <;> unfold missing_pass_signed <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    infer_instance

lemma missing_pass_signed_sum (u : Bool) :
    (1/4:ℝ≥0∞) • missing_pass_signed u + (1/4:ℝ≥0∞) • missing_pass_signed (!u) =
      (1/2:ℝ≥0∞) • laplaceRate 1 := by
  rw [missing_pass_laplace_split 1 (by norm_num), smul_add, smul_smul, smul_smul,
    missing_pass_half_sq, missing_pass_exp_one]
  cases u <;> simp [missing_pass_signed, add_comm]

def missing_pass_pairLaw (a : Fin 2) : Measure (ℝ × Bool) :=
  if a = 0 then
    (1/2:ℝ≥0∞) • (laplaceRate 1).map (fun x => (x,true)) +
    (1/2:ℝ≥0∞) • (laplaceRate 2).map (fun x => (x,false))
  else
    (3/4:ℝ≥0∞) • (laplaceRate 1).map (fun x => (x,true)) +
    (1/4:ℝ≥0∞) • (laplaceRate 1).map (fun x => (x,false))

lemma missing_pass_joint (u : Bool) (a : Fin 2) :
    (missingPassLaw u).map (fun ω => ((potentialY a ω, potentialS a ω), assignment ω)) =
      (missing_pass_pairLaw a).prod fairAssignment := by
  have hm : Measurable (fun ω : State 2 0 => ((potentialY a ω, potentialS a ω), assignment ω)) := by
    fun_prop
  have hsum := congrArg (Measure.map (fun x : ℝ => (x,true))) (missing_pass_signed_sum u)
  have hmap : Measurable (fun x : ℝ => (x,true)) := by fun_prop
  simp only [Measure.map_add _ _ hmap, Measure.map_smul _ hmap.aemeasurable] at hsum
  have hdef : missingPassLaw u =
    (1/4:ℝ≥0∞) • stratumLaw true true (missing_pass_signed u) (laplaceRate 1) +
    (1/4:ℝ≥0∞) • stratumLaw true false (missing_pass_signed (!u)) (laplaceRate 1) +
    (1/2:ℝ≥0∞) • stratumLaw false true (laplaceRate 2) (laplaceRate 1) := by
    cases u <;> rfl
  rw [hdef]
  simp only [Measure.map_add _ _ hm, Measure.map_smul _ hm.aemeasurable, missing_pass_stratum_joint]
  fin_cases a
  · simp only [show (⟨0, by omega⟩ : Fin 2) = 0 from rfl, ite_true]
    rw [← Measure.prod_smul_left, ← Measure.prod_smul_left, ← Measure.prod_smul_left,
      ← Measure.add_prod, ← Measure.add_prod, hsum]
    simp [missing_pass_pairLaw, Fin.ext_iff]
  · simp only [show (⟨1, by omega⟩ : Fin 2) ≠ 0 from by decide, ite_false]
    rw [← Measure.prod_smul_left, ← Measure.prod_smul_left, ← Measure.prod_smul_left,
      ← Measure.add_prod, ← Measure.add_prod]
    rw [add_right_comm, ← add_smul, missing_pass_quarter_half]
    simp [missing_pass_pairLaw, Fin.ext_iff]

lemma missing_pass_pair_marginal (u : Bool) (a : Fin 2) :
    (missingPassLaw u).map (fun ω => (potentialY a ω, potentialS a ω)) =
      missing_pass_pairLaw a := by
  have he := congrArg (Measure.map Prod.fst) (missing_pass_joint u a)
  rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod,
    measure_univ, one_smul] at he
  exact he

local instance missing_pass_pair_prob (a : Fin 2) : IsProbabilityMeasure (missing_pass_pairLaw a) := by
  letI := missing_pass_prob false
  rw [← missing_pass_pair_marginal false a]
  infer_instance

lemma missing_pass_assignment_marginal (u : Bool) :
    (missingPassLaw u).map assignment = fairAssignment := by
  letI := missing_pass_prob u
  have he := congrArg (Measure.map Prod.snd) (missing_pass_joint u 0)
  rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod,
    ← missing_pass_pair_marginal u 0, measure_univ, one_smul] at he
  exact he

lemma missing_pass_ignorability (u : Bool) : Ignorability (missingPassLaw u) := by
  letI := missing_pass_prob u
  constructor
  · intro a
    apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).mpr
    rw [missing_pass_joint, missing_pass_pair_marginal, missing_pass_assignment_marginal]
  · intro a
    have ha : missingPassLaw u (armEvent a) = 1/2 := by
      have he := congrArg (fun μ : Measure (Fin 2) => μ {a}) (missing_pass_assignment_marginal u)
      rw [Measure.map_apply measurable_assignment (measurableSet_singleton a)] at he
      change missingPassLaw u (armEvent a) = _ at he
      rw [he]
      fin_cases a <;> simp [fairAssignment, Fin.ext_iff]
    rw [ha]
    norm_num [one_div]

lemma missing_pass_fair_singleton (a : Fin 2) : fairAssignment {a} = 1/2 := by
  fin_cases a <;> simp [fairAssignment, Fin.ext_iff]


lemma missing_pass_arm_pair (u : Bool) (a : Fin 2) :
    ((missingPassLaw u).restrict (armEvent a)).map (fun ω => (observedY ω, observedS ω)) =
      (1/2:ℝ≥0∞) • missing_pass_pairLaw a := by
  ext B hB
  rw [Measure.map_apply (by fun_prop) hB, Measure.restrict_apply ((by fun_prop :
    Measurable (fun ω : State 2 0 => (observedY ω, observedS ω))) hB),
    Measure.smul_apply, smul_eq_mul]
  have he := congrArg (fun μ : Measure ((ℝ × Bool) × Fin 2) => μ (B ×ˢ {a}))
    (missing_pass_joint u a)
  rw [Measure.map_apply (by fun_prop) (hB.prod (measurableSet_singleton a)),
    Measure.prod_prod, missing_pass_fair_singleton, mul_comm] at he
  rw [← he]
  congr 1
  ext ω
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_singleton_iff, armEvent, mem_ofPred_eq]
  constructor <;> rintro ⟨h,hz⟩ <;>
    exact ⟨by simpa only [observedY, observedS, hz] using h, hz⟩

lemma missing_pass_arm_compl : (armEvent 0 : Set (State 2 0))ᶜ = armEvent 1 := by
  ext ω
  simp only [armEvent, mem_compl_iff, mem_ofPred_eq]
  have ha : assignment ω = 0 ∨ assignment ω = 1 := by
    have := (assignment ω).isLt
    rcases assignment ω with ⟨i,hi⟩
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp
  rcases ha with h | h <;> simp [h]

lemma missing_pass_arm_partition (u : Bool) :
    missingPassLaw u = (missingPassLaw u).restrict (armEvent 0) +
      (missingPassLaw u).restrict (armEvent 1) := by
  rw [← missing_pass_arm_compl]
  exact (Measure.restrict_add_restrict_compl (measurableSet_arm 0)).symm

lemma missing_pass_pair_outcomes :
    (missing_pass_pairLaw 0).map Prod.fst =
      (1/2:ℝ≥0∞) • laplaceRate 1 + (1/2:ℝ≥0∞) • laplaceRate 2 ∧
    (missing_pass_pairLaw 1).map Prod.fst = laplaceRate 1 := by
  have htag (r : ℝ) (b : Bool) :
      ((laplaceRate r).map (fun x => (x,b))).map Prod.fst = laplaceRate r := by
    rw [Measure.map_map measurable_fst (by fun_prop)]
    exact Measure.map_id
  constructor
  · simp [missing_pass_pairLaw, Measure.map_add _ _ measurable_fst,
      Measure.map_smul _ measurable_fst.aemeasurable, htag]
  · have hs : (3/4:ℝ≥0∞) + 1/4 = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num
    simp only [missing_pass_pairLaw, show (1:Fin 2) ≠ 0 from by decide, ite_false,
      Measure.map_add _ _ measurable_fst, Measure.map_smul _ measurable_fst.aemeasurable, htag,
      ← add_smul, hs, one_smul]

lemma missing_pass_arm_outcome (u : Bool) (a : Fin 2) :
    ((missingPassLaw u).restrict (armEvent a)).map observedY =
      (1/2:ℝ≥0∞) • (missing_pass_pairLaw a).map Prod.fst := by
  have he := congrArg (Measure.map Prod.fst) (missing_pass_arm_pair u a)
  rw [Measure.map_map measurable_fst (by fun_prop),
    Measure.map_smul _ measurable_fst.aemeasurable] at he
  exact he

lemma missing_pass_observed_law (u : Bool) :
    (missingPassLaw u).map observedY =
      (3/4:ℝ≥0∞) • laplaceRate 1 + (1/4:ℝ≥0∞) • laplaceRate 2 := by
  conv_lhs => rw [missing_pass_arm_partition u]
  rw [Measure.map_add _ _ measurable_observedY, missing_pass_arm_outcome,
    missing_pass_arm_outcome, missing_pass_pair_outcomes.1, missing_pass_pair_outcomes.2,
    smul_add, smul_smul, smul_smul, missing_pass_half_sq, add_right_comm,
    ← add_smul, missing_pass_quarter_half]

lemma missing_pass_stratum_outcome0 (s t : Bool) (F G : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G] :
    (stratumLaw s t F G).map (potentialY 0) = F := by
  unfold stratumLaw
  rw [Measure.map_map (measurable_potentialY 0) (by fun_prop)]
  change ((F.prod G).prod fairAssignment).map (Prod.fst ∘ Prod.fst) = F
  rw [← Measure.map_map measurable_fst measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul, Measure.map_fst_prod, measure_univ, one_smul]

lemma missing_pass_stratum_allpass (s t : Bool) (F G : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G] :
    (stratumLaw s t F G).restrict alwaysPass =
      if s = true ∧ t = true then stratumLaw s t F G else 0 := by
  unfold stratumLaw
  rw [Measure.restrict_map (by fun_prop) measurableSet_always]
  have hp : (fun ω : (ℝ × ℝ) × Fin 2 => (![ω.1.1,ω.1.2], ![s,t], ω.2, fun _ : Fin 0 => (0:ℝ))) ⁻¹'
      alwaysPass = if s = true ∧ t = true then univ else ∅ := by
    cases s <;> cases t <;> ext ω <;>
      simp [alwaysPass, potentialS, Fin.forall_fin_two]
  rw [hp]
  split_ifs <;> simp

lemma missing_pass_allpass_law (u : Bool) :
    ((missingPassLaw u).restrict alwaysPass).map (potentialY 0) =
      (1/4:ℝ≥0∞) • missing_pass_signed u := by
  cases u <;>
    simp only [missingPassLaw, Bool.false_eq_true, ite_false, ite_true, Measure.restrict_add,
      Measure.restrict_smul, missing_pass_stratum_allpass, and_self, ↓reduceIte,
      Bool.false_eq_true, and_false, false_and, smul_zero, add_zero, zero_add,
      Measure.map_smul _ (measurable_potentialY 0).aemeasurable,
      missing_pass_stratum_outcome0, missing_pass_signed]

lemma missing_pass_allpass_mass (u : Bool) : missingPassLaw u alwaysPass = 1/4 := by
  have he := congrArg (fun ν : Measure ℝ => ν univ) (missing_pass_allpass_law u)
  simpa only [Measure.map_apply (measurable_potentialY 0) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one] using he

lemma missing_pass_pair_pass (a : Fin 2) (B : Set ℝ) (hB : MeasurableSet B) :
    missing_pass_pairLaw a (B ×ˢ {true}) =
      (if a = 0 then (1/2:ℝ≥0∞) else 3/4) * laplaceRate 1 B := by
  have htag (F : Measure ℝ) (b : Bool) :
      (F.map (fun x => (x,b))) (B ×ˢ {true}) = if b = true then F B else 0 := by
    rw [Measure.map_apply (by fun_prop) (hB.prod (measurableSet_singleton true))]
    cases b <;> simp
  fin_cases a <;> simp [missing_pass_pairLaw, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, htag, Fin.ext_iff]

lemma missing_pass_rates (u : Bool) :
    passingRate (missingPassLaw u) 0 = 1/2 ∧ passingRate (missingPassLaw u) 1 = 3/4 ∧
    trimRatio (missingPassLaw u) 0 = 1/2 := by
  letI := missing_pass_prob u
  have hr := (nonzero_passing_corrected (missingPassLaw u) inferInstance
    (missing_pass_ignorability u)).1
  have hp (a : Fin 2) : missingPassLaw u (potentialPass a) =
      if a = 0 then (1/2:ℝ≥0∞) else 3/4 := by
    have he := congrArg (fun ν : Measure (ℝ × Bool) => ν (univ ×ˢ {true}))
      (missing_pass_pair_marginal u a)
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod (measurableSet_singleton true)),
      missing_pass_pair_pass a univ MeasurableSet.univ, measure_univ, mul_one] at he
    simpa only [preimage, mem_prod, mem_univ, mem_singleton_iff, true_and, potentialPass] using he
  have h0 : passingRate (missingPassLaw u) 0 = 1/2 := by
    rw [hr, hp]
    norm_num
  have h1 : passingRate (missingPassLaw u) 1 = 3/4 := by
    rw [hr, hp]
    norm_num
  refine ⟨h0,h1,?_⟩
  norm_num [trimRatio, Fin.sum_univ_two, h0, h1]

lemma missing_pass_assumptions (u : Bool) : Assumptions (missingPassLaw u) := by
  refine ⟨missing_pass_prob u, missing_pass_ignorability u, ?_⟩
  intro a
  have hr := missing_pass_rates u
  fin_cases a
  · change 0 < passingRate (missingPassLaw u) 0
    rw [hr.1]; norm_num
  · change 0 < passingRate (missingPassLaw u) 1
    rw [hr.2.1]; norm_num

lemma missing_pass_passer_sublaw (u : Bool) :
    ((missingPassLaw u).restrict (passEvent ∩ armEvent 0)).map observedY =
      (1/4:ℝ≥0∞) • laplaceRate 1 := by
  ext B hB
  rw [Measure.map_apply measurable_observedY hB, Measure.restrict_apply (measurable_observedY hB),
    Measure.smul_apply, smul_eq_mul]
  have he := congrArg (fun ν : Measure (ℝ × Bool) => ν (B ×ˢ {true}))
    (missing_pass_arm_pair u 0)
  rw [Measure.map_apply (by fun_prop) (hB.prod (measurableSet_singleton true)),
    Measure.restrict_apply ((by fun_prop : Measurable
      (fun ω : State 2 0 => (observedY ω,observedS ω)))
      (hB.prod (measurableSet_singleton true))),
    Measure.smul_apply, smul_eq_mul, missing_pass_pair_pass 0 B hB,
    ite_eq_left rfl, ← mul_assoc, missing_pass_half_sq] at he
  rw [← he]
  congr 1
  ext ω
  simp [passEvent, and_assoc]

lemma missing_pass_passer_mass (u : Bool) : missingPassLaw u (passEvent ∩ armEvent 0) = 1/4 := by
  have he := congrArg (fun ν : Measure ℝ => ν univ) (missing_pass_passer_sublaw u)
  simpa only [Measure.map_apply measurable_observedY MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using he

lemma missing_pass_passer_law (u : Bool) : passerLaw (missingPassLaw u) 0 = laplaceRate 1 := by
  unfold passerLaw eventLaw
  rw [missing_pass_passer_mass, missing_pass_passer_sublaw, smul_smul]
  have hs : ((1/4:ℝ≥0∞)⁻¹)*(1/4) = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  rw [hs, one_smul]

lemma missing_pass_observable_arm (u : Bool) (a : Fin 2) :
    ((missingPassLaw u).restrict (armEvent a)).map
      (fun ω => (observedY ω, observedS ω, assignment ω)) =
    (1/2:ℝ≥0∞) • (missing_pass_pairLaw a).map (fun p => (p.1,p.2,a)) := by
  have he := congrArg (Measure.map (fun p : ℝ × Bool => (p.1,p.2,a)))
    (missing_pass_arm_pair u a)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_smul _ (by fun_prop)] at he
  rw [← he]
  apply Measure.map_congr
  filter_upwards [self_mem_ae_restrict (measurableSet_arm a)] with ω hω
  change assignment ω = a at hω
  simp [Function.comp_def, hω]

lemma missing_pass_observables_equal :
    (missingPassLaw false).map (fun ω => (observedY ω, observedS ω, assignment ω)) =
      (missingPassLaw true).map (fun ω => (observedY ω, observedS ω, assignment ω)) := by
  conv_lhs => rw [missing_pass_arm_partition false]
  conv_rhs => rw [missing_pass_arm_partition true]
  simp only [Measure.map_add _ _ (show Measurable (fun ω : State 2 0 =>
    (observedY ω, observedS ω, assignment ω)) from by fun_prop), missing_pass_observable_arm]

lemma missing_pass_atomless (u : Bool) : Atomless ((missingPassLaw u).map observedY) := by
  rw [missing_pass_observed_law]
  intro x
  simp [Measure.add_apply, Measure.smul_apply, missing_pass_laplace_atomless 1 x,
    missing_pass_laplace_atomless 2 x]

lemma missing_pass_support (u : Bool) : FullRealSupport (missingPassLaw u) observedY := by
  intro l v hlv
  have he := congrArg (fun ν : Measure ℝ => ν (Ioo l v)) (missing_pass_observed_law u)
  rw [Measure.map_apply measurable_observedY measurableSet_Ioo,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul] at he
  change 0 < missingPassLaw u (observedY ⁻¹' Ioo l v)
  rw [he]
  apply add_pos_of_pos_of_nonneg _ zero_le
  exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.div_pos (by norm_num) (by norm_num),
    missing_pass_laplace_support 1 (by norm_num) l v hlv⟩

lemma missing_pass_moments (u : Bool) : AllMoments (missingPassLaw u) observedY := by
  intro n
  have hi : Integrable (fun x : ℝ => |x|^n) ((missingPassLaw u).map observedY) := by
    rw [missing_pass_observed_law, integrable_add_measure]
    exact ⟨(missing_pass_laplace_moments 1 (by norm_num) n).smul_measure (by finiteness),
      (missing_pass_laplace_moments 2 (by norm_num) n).smul_measure (by norm_num)⟩
  exact hi.comp_measurable measurable_observedY

/-- Push the restricted law forward before computing an event mean. -/
lemma missing_pass_mean_push {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : Measurable f) (E : Set Ω) (B : Set ℝ) (hB : MeasurableSet B) :
    eventMean μ f ((f ⁻¹' B) ∩ E) = eventMean ((μ.restrict E).map f) (fun x => x) B := by
  unfold eventMean
  rw [setIntegral_map hB measurable_id'.aestronglyMeasurable hf.aemeasurable,
    Measure.map_apply hf hB, Measure.restrict_apply (hf hB),
    Measure.restrict_restrict (hf hB)]

lemma missing_pass_mean_smul (ν : Measure ℝ) (B : Set ℝ) (c : ℝ≥0∞) (hc : c.toReal ≠ 0) :
    eventMean (c • ν) (fun x => x) B = eventMean ν (fun x => x) B := by
  unfold eventMean
  rw [Measure.restrict_smul, integral_smul_measure, Measure.smul_apply]
  simp only [smul_eq_mul, ENNReal.toReal_mul]
  exact mul_div_mul_left _ _ hc

lemma missing_pass_signed_mean (u : Bool) :
    (∫ x : ℝ, x ∂missing_pass_signed u) = if u then 1 else -1 := by
  have he : (∫ x : ℝ, x ∂exponentialOne) = 1 := by
    rw [← missing_pass_exp_one, missing_pass_exp_mean 1 (by norm_num)]
    norm_num
  cases u
  · simp only [missing_pass_signed, Bool.false_eq_true, ite_false]
    rw [integral_map measurable_neg.aemeasurable measurable_id'.aestronglyMeasurable,
      integral_neg, he]
  · simp only [missing_pass_signed, ite_true]
    exact he

lemma missing_pass_target_mean (u : Bool) :
    eventMean (missingPassLaw u) (potentialY 0) alwaysPass = if u then 1 else -1 := by
  unfold eventMean
  have he := integral_map (μ := (missingPassLaw u).restrict alwaysPass)
    (measurable_potentialY 0).aemeasurable measurable_id'.aestronglyMeasurable
  change (∫ x : ℝ, x ∂((missingPassLaw u).restrict alwaysPass).map (potentialY 0)) =
    (∫ ω in alwaysPass, potentialY 0 ω ∂missingPassLaw u) at he
  rw [← he, missing_pass_allpass_law, integral_smul_measure, missing_pass_allpass_mass,
    missing_pass_signed_mean]
  cases u <;> norm_num

lemma missing_pass_mixture_tail_means :
    eventMean ((1/2:ℝ≥0∞) • laplaceRate 1 + (1/2:ℝ≥0∞) • laplaceRate 2)
      (fun x => x) (Iic 0) = -3/4 ∧
    eventMean ((1/2:ℝ≥0∞) • laplaceRate 1 + (1/2:ℝ≥0∞) • laplaceRate 2)
      (fun x => x) (Ici 0) = 3/4 := by
  have h1 := missing_pass_laplace_halves 1 (by norm_num)
  have h2 := missing_pass_laplace_halves 2 (by norm_num)
  have hi1 := (missing_pass_integrable_id (missing_pass_laplace_moments 1 (by norm_num) 1)).smul_measure
    (by norm_num : (1/2:ℝ≥0∞) ≠ ∞)
  have hi2 := (missing_pass_integrable_id (missing_pass_laplace_moments 2 (by norm_num) 1)).smul_measure
    (by norm_num : (1/2:ℝ≥0∞) ≠ ∞)
  constructor <;> unfold eventMean <;>
    rw [Measure.restrict_add, integral_add_measure hi1.integrableOn hi2.integrableOn] <;>
    norm_num [Measure.restrict_smul, integral_smul_measure, Measure.add_apply,
      Measure.smul_apply, smul_eq_mul, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2,
      h2.1, h2.2.1, h2.2.2.1, h2.2.2.2, ENNReal.toReal_add, ENNReal.toReal_mul] <;>
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)] <;> norm_num

lemma missing_pass_printed_means (u : Bool) :
    eventMean (missingPassLaw u) observedY ({ω | observedY ω ≤ 0} ∩ armEvent 0) = -3/4 ∧
    eventMean (missingPassLaw u) observedY ({ω | 0 ≤ observedY ω} ∩ armEvent 0) = 3/4 := by
  have h0 := missing_pass_mean_push (missingPassLaw u) observedY measurable_observedY
    (armEvent 0) (Iic 0) measurableSet_Iic
  have h1 := missing_pass_mean_push (missingPassLaw u) observedY measurable_observedY
    (armEvent 0) (Ici 0) measurableSet_Ici
  rw [missing_pass_arm_outcome, missing_pass_pair_outcomes.1,
    missing_pass_mean_smul _ _ _ (by norm_num), missing_pass_mixture_tail_means.1] at h0
  rw [missing_pass_arm_outcome, missing_pass_pair_outcomes.1,
    missing_pass_mean_smul _ _ _ (by norm_num), missing_pass_mixture_tail_means.2] at h1
  exact ⟨h0,h1⟩

lemma missing_pass_corrected_means (u : Bool) :
    lowerBound (missingPassLaw u) 0 = -1 ∧ upperBound (missingPassLaw u) 0 = 1 := by
  have hq : quantile (passerLaw (missingPassLaw u) 0) (1/2) = 0 := by
    rw [missing_pass_passer_law, missing_pass_laplace_median]
  have htrim := (missing_pass_rates u).2.2
  have h1 := missing_pass_laplace_halves 1 (by norm_num)
  have hlow : eventMean (laplaceRate 1) (fun x => x) (Iic 0) = -1 := by
    norm_num [eventMean, h1.1, h1.2.2.1]
  have hupp : eventMean (laplaceRate 1) (fun x => x) (Ici 0) = 1 := by
    norm_num [eventMean, h1.2.1, h1.2.2.2]
  constructor
  · unfold lowerBound
    rw [htrim]
    norm_num only [show (1:ℝ) - 1/2 = 1/2 by norm_num]
    rw [hq]
    simp only [← EReal.coe_zero, EReal.coe_le_coe_iff]
    rw [inter_comm]
    change eventMean (missingPassLaw u) observedY
      ((observedY ⁻¹' Iic 0) ∩ (passEvent ∩ armEvent 0)) = -1
    rw [missing_pass_mean_push _ _ measurable_observedY _ _ measurableSet_Iic,
      missing_pass_passer_sublaw, missing_pass_mean_smul _ _ _ (by norm_num), hlow]
  · unfold upperBound
    rw [htrim, hq]
    simp only [← EReal.coe_zero, EReal.coe_le_coe_iff]
    rw [inter_comm]
    change eventMean (missingPassLaw u) observedY
      ((observedY ⁻¹' Ici 0) ∩ (passEvent ∩ armEvent 0)) = 1
    rw [missing_pass_mean_push _ _ measurable_observedY _ _ measurableSet_Ici,
      missing_pass_passer_sublaw, missing_pass_mean_smul _ _ _ (by norm_num), hupp]

theorem missing_passing_condition_counterexample_proof :
    (∀ upper : Bool, let μ := missingPassLaw upper
      Assumptions μ ∧ μ alwaysPass = 1/4 ∧ Atomless (μ.map observedY) ∧
      FullRealSupport μ observedY ∧ AllMoments μ observedY ∧
      passingRate μ 0 = 1/2 ∧ passingRate μ 1 = 3/4 ∧ trimRatio μ 0 = 1/2 ∧
      passerLaw μ 0 = laplaceRate 1 ∧ quantile (passerLaw μ 0) (1/2) = 0 ∧
      eventMean μ observedY ({ω | observedY ω ≤ 0} ∩ armEvent 0) = -3/4 ∧
      eventMean μ observedY ({ω | 0 ≤ observedY ω} ∩ armEvent 0) = 3/4 ∧
      eventMean μ (potentialY 0) alwaysPass = (if upper then 1 else -1) ∧
      ¬ (eventMean μ observedY ({ω | observedY ω ≤ 0} ∩ armEvent 0) ≤
          eventMean μ (potentialY 0) alwaysPass ∧
        eventMean μ (potentialY 0) alwaysPass ≤
          eventMean μ observedY ({ω | 0 ≤ observedY ω} ∩ armEvent 0)) ∧
      lowerBound μ 0 = -1 ∧ upperBound μ 0 = 1) ∧
    (missingPassLaw false).map (fun ω => (observedY ω, observedS ω, assignment ω)) =
      (missingPassLaw true).map (fun ω => (observedY ω, observedS ω, assignment ω)) := by
  refine ⟨?_, missing_pass_observables_equal⟩
  intro u
  dsimp only
  have hr := missing_pass_rates u
  have hm := missing_pass_printed_means u
  have ht := missing_pass_target_mean u
  have hc := missing_pass_corrected_means u
  have hq : quantile (passerLaw (missingPassLaw u) 0) (1/2) = 0 := by
    rw [missing_pass_passer_law, missing_pass_laplace_median]
  refine ⟨missing_pass_assumptions u, missing_pass_allpass_mass u, missing_pass_atomless u,
    missing_pass_support u, missing_pass_moments u, hr.1, hr.2.1, hr.2.2,
    missing_pass_passer_law u, hq, hm.1, hm.2, ht, ?_, hc.1, hc.2⟩
  rw [hm.1, hm.2, ht]
  cases u <;> norm_num

end
end AronowAudit.P010.Wave1
