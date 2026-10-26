import AronowAudit.P010.P010_Population
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace AronowAudit.P010.Wave1

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical Topology

noncomputable section

/-! Exact density calculations for the beta/heavy-tail witness. -/

def t5_betaDensity (x : ℝ) : ℝ := 30*x^2*(1-x)^2

lemma t5_betaDensity_nonneg (x : ℝ) : 0 ≤ t5_betaDensity x := by
  unfold t5_betaDensity
  positivity

lemma t5_betaDensity_measurable : Measurable t5_betaDensity := by
  unfold t5_betaDensity
  fun_prop

lemma t5_beta_restrict :
    beta33 = (volume.restrict (Ioo (0:ℝ) 1)).withDensity
      (fun x => ENNReal.ofReal (t5_betaDensity x)) := by
  rw [← withDensity_indicator measurableSet_Ioo]
  unfold beta33
  congr 1
  funext x
  by_cases hx : x ∈ Ioo (0:ℝ) 1 <;>
    simp [Set.indicator, hx, t5_betaDensity, show (0 < x ∧ x < 1) ↔ x ∈ Ioo (0:ℝ) 1 from Iff.rfl]

lemma t5_beta_integral (g : ℝ → ℝ) :
    (∫ x, g x ∂beta33) = ∫ x in Ioo (0:ℝ) 1, t5_betaDensity x * g x := by
  rw [t5_beta_restrict, integral_withDensity_eq_integral_toReal_smul
    t5_betaDensity_measurable.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (t5_betaDensity_nonneg _), smul_eq_mul]

lemma t5_beta_integrable_iff (g : ℝ → ℝ) :
    Integrable g beta33 ↔
      IntegrableOn (fun x => t5_betaDensity x * g x) (Ioo (0:ℝ) 1) := by
  rw [t5_beta_restrict, integrable_withDensity_iff
    t5_betaDensity_measurable.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (t5_betaDensity_nonneg _), mul_comm, IntegrableOn]

lemma t5_beta_integrable_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable g beta33 := by
  rw [t5_beta_integrable_iff]
  have hc : Continuous (fun x => t5_betaDensity x * g x) :=
    (show Continuous t5_betaDensity by unfold t5_betaDensity; fun_prop).mul hg
  exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self

lemma t5_beta_pow_integral (n : ℕ) :
    (∫ x, x^n ∂beta33) =
      30 / (n+3:ℝ) - 60 / (n+4:ℝ) + 30 / (n+5:ℝ) := by
  rw [t5_beta_integral, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have he : (fun x : ℝ => t5_betaDensity x * x^n) =
      fun x => 30*x^(n+2) - 60*x^(n+3) + 30*x^(n+4) := by
    funext x
    simp only [t5_betaDensity, pow_add]
    ring
  rw [he, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow]
  · simp [Nat.cast_add, Nat.cast_ofNat]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

lemma t5_beta_probability : IsProbabilityMeasure beta33 := by
  have hi : Integrable (fun _ : ℝ => (1:ℝ)) beta33 :=
    t5_beta_integrable_continuous continuous_const
  have hm := t5_beta_pow_integral 0
  norm_num at hm
  have hf : IsFiniteMeasure beta33 := ⟨by
    simpa only [hasFiniteIntegral_iff_enorm, enorm_one, lintegral_one] using hi.hasFiniteIntegral⟩
  letI := hf
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top beta33 univ) (by simp)).mp
  simpa [measureReal_def] using hm

local instance t5_instBetaProbability : IsProbabilityMeasure beta33 := t5_beta_probability

lemma t5_beta_ae : ∀ᵐ x ∂beta33, x ∈ Ioo (0:ℝ) 1 := by
  rw [t5_beta_restrict]
  exact (ae_restrict_mem measurableSet_Ioo).filter_mono
    (withDensity_absolutelyContinuous _ _).ae_le

lemma t5_beta_moments :
    (∫ x : ℝ, x ∂beta33) = 1/2 ∧
    (∫ x : ℝ, x^2 ∂beta33) = 2/7 ∧
    (∫ x : ℝ, |x|^3 ∂beta33) = 5/28 := by
  have h1 := t5_beta_pow_integral 1
  have h2 := t5_beta_pow_integral 2
  have h3 := t5_beta_pow_integral 3
  norm_num at h1 h2 h3
  refine ⟨h1, h2, ?_⟩
  rw [integral_congr_ae (by
    filter_upwards [t5_beta_ae] with x hx
    rw [abs_of_pos hx.1])]
  exact h3

lemma t5_beta_partial (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    (∫ x in Ioo 0 t, x^n ∂beta33) =
      30*t^(n+3)/(n+3:ℝ) - 60*t^(n+4)/(n+4:ℝ) + 30*t^(n+5)/(n+5:ℝ) := by
  rw [beta33, setIntegral_withDensity_eq_setIntegral_toReal_smul
    (by
      apply Measurable.ennreal_ofReal
      exact Measurable.ite (measurableSet_Ioo (a := (0:ℝ)) (b := 1))
        (by fun_prop) measurable_const) (by simp) _ measurableSet_Ioo]
  have he : (fun x : ℝ =>
      (ENNReal.ofReal (if 0 < x ∧ x < 1 then 30*x^2*(1-x)^2 else 0)).toReal • x^n)
      =ᵐ[volume.restrict (Ioo 0 t)]
      (fun x => 30*x^(n+2) - 60*x^(n+3) + 30*x^(n+4)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [if_pos (show 0 < x ∧ x < 1 from ⟨hx.1, lt_of_lt_of_le hx.2 ht1⟩),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 30*x^2*(1-x)^2), smul_eq_mul,
      pow_add]
    ring
  rw [integral_congr_ae he, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow]
  · simp [Nat.cast_add, Nat.cast_ofNat]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

lemma t5_beta_cdf (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (beta33 (Ioo 0 t)).toReal = 10*t^3 - 15*t^4 + 6*t^5 := by
  have h := t5_beta_partial t ht ht1 0
  norm_num [integral_const, measureReal_def] at h
  rw [h]
  ring

lemma t5_shift_inv_integral (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    IntegrableOn (fun x : ℝ => 1/(1+x)^(n+2)) (Ioi R) ∧
    (∫ x in Ioi R, (1/(1+x)^(n+2) : ℝ)) =
      1/((n+1:ℝ)*(1+R)^(n+1)) := by
  have hd : ∀ x ∈ Ici R, HasDerivAt
      (fun y : ℝ => -(1/(1+y)^(n+1))/(n+1:ℝ)) (1/(1+x)^(n+2)) x := by
    intro x hx
    have hx0 : 1+x ≠ 0 := by linarith [hx.out]
    have hd := (((hasDerivAt_id' x).const_add 1).pow (n+1)).inv (pow_ne_zero _ hx0)
    convert hd.neg.div_const (n+1:ℝ) using 1 <;>
      simp [one_div, Nat.cast_add, Nat.cast_one, pow_succ] <;> field_simp <;> ring
  have ht : Tendsto (fun y : ℝ => -(1/(1+y)^(n+1))/(n+1:ℝ)) atTop (𝓝 0) := by
    have ht0 : Tendsto (fun y : ℝ => 1+y) atTop atTop :=
      tendsto_const_nhds.add_atTop tendsto_id
    have ht1 := tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by omega : n+1 ≠ 0)).comp ht0)
    simpa only [one_div, neg_zero, zero_div, Function.comp_def] using ht1.neg.div_const (n+1:ℝ)
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd
    (fun x hx => by
      have hx0 : 0 < 1+x := by linarith [hx.out]
      positivity : ∀ x ∈ Ioi R, 0 ≤ (1/(1+x)^(n+2) : ℝ)) ht
  refine ⟨hi, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht]
  simp only [zero_sub, neg_div, neg_neg, one_div, mul_inv_rev, div_eq_mul_inv]
  ring

def t5_heavyDensity (x : ℝ) : ℝ := 5/(2*(1+|x|)^6)

lemma t5_heavyDensity_nonneg (x : ℝ) : 0 ≤ t5_heavyDensity x := by
  unfold t5_heavyDensity
  positivity

lemma t5_heavyDensity_measurable : Measurable t5_heavyDensity := by
  unfold t5_heavyDensity
  fun_prop

lemma t5_heavy_integral (g : ℝ → ℝ) :
    (∫ x, g x ∂heavySix) = ∫ x, t5_heavyDensity x * g x := by
  change (∫ x, g x ∂volume.withDensity (fun x => ENNReal.ofReal (t5_heavyDensity x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    t5_heavyDensity_measurable.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (t5_heavyDensity_nonneg _), smul_eq_mul]

lemma t5_heavy_integrable_iff (g : ℝ → ℝ) :
    Integrable g heavySix ↔ Integrable (fun x => t5_heavyDensity x * g x) := by
  change Integrable g (volume.withDensity (fun x => ENNReal.ofReal (t5_heavyDensity x))) ↔ _
  rw [integrable_withDensity_iff
    t5_heavyDensity_measurable.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (t5_heavyDensity_nonneg _), mul_comm]

lemma t5_heavy_positive_half (k : Fin 4) :
    IntegrableOn (fun x : ℝ => t5_heavyDensity x * |x|^(k:ℕ)) (Ioi 0) ∧
    (∫ x in Ioi 0, t5_heavyDensity x * |x|^(k:ℕ)) =
      ![(1/2:ℝ), 1/8, 1/12, 1/8] k := by
  have h2 := t5_shift_inv_integral 0 0 (by norm_num)
  have h3 := t5_shift_inv_integral 1 0 (by norm_num)
  have h4 := t5_shift_inv_integral 2 0 (by norm_num)
  have h5 := t5_shift_inv_integral 3 0 (by norm_num)
  have h6 := t5_shift_inv_integral 4 0 (by norm_num)
  norm_num at h2 h3 h4 h5 h6
  have he (x : ℝ) (hx : x ∈ Ioi (0:ℝ)) :
      t5_heavyDensity x * |x|^(k:ℕ) =
      ![(5/2:ℝ)*(1/(1+x)^6),
        (5/2:ℝ)*((1/(1+x)^5)-(1/(1+x)^6)),
        (5/2:ℝ)*((1/(1+x)^4)-2*(1/(1+x)^5)+(1/(1+x)^6)),
        (5/2:ℝ)*((1/(1+x)^3)-3*(1/(1+x)^4)+3*(1/(1+x)^5)-(1/(1+x)^6))] k := by
    have hx0 : 1+x ≠ 0 := by linarith [hx.out]
    fin_cases k <;> simp [t5_heavyDensity, abs_of_pos hx.out] <;> field_simp <;> ring
  have hea := (ae_restrict_mem (μ := volume) measurableSet_Ioi).mono (fun x hx => he x hx)
  constructor
  · apply (integrable_congr hea).mpr
    fin_cases k <;> dsimp
    · simpa only [one_div, Pi.sub_apply, Pi.add_apply] using h6.1.const_mul (5/2:ℝ)
    · simpa only [one_div, Pi.sub_apply, Pi.add_apply] using (h5.1.integrable.sub' h6.1).const_mul (5/2:ℝ)
    · simpa only [one_div, Pi.sub_apply, Pi.add_apply] using ((h4.1.integrable.sub' (h5.1.const_mul 2)).fun_add h6.1).const_mul (5/2:ℝ)
    · simpa only [one_div, Pi.sub_apply, Pi.add_apply] using (((h3.1.integrable.sub' (h4.1.const_mul 3)).add
        (h5.1.const_mul 3)).sub' h6.1).const_mul (5/2:ℝ)
  · rw [integral_congr_ae hea]
    fin_cases k <;> dsimp <;> simp only [one_div]
    · rw [integral_const_mul, h6.2]
      norm_num
    · rw [integral_const_mul, integral_sub h5.1 h6.1, h5.2, h6.2]
      norm_num
    · rw [integral_const_mul, integral_add (h4.1.integrable.sub' (h5.1.const_mul 2)) h6.1,
        integral_sub h4.1 (h5.1.const_mul 2), integral_const_mul, h4.2, h5.2, h6.2]
      norm_num
    · rw [integral_const_mul,
        integral_sub ((h3.1.integrable.sub' (h4.1.const_mul 3)).fun_add (h5.1.const_mul 3)) h6.1,
        integral_add (h3.1.integrable.sub' (h4.1.const_mul 3)) (h5.1.const_mul 3),
        integral_sub h3.1 (h4.1.const_mul 3), integral_const_mul,
        integral_const_mul, h3.2, h4.2, h5.2, h6.2]
      norm_num

lemma t5_even_halves (f : ℝ → ℝ) (he : ∀ x, f (-x) = f x)
    (hi : IntegrableOn f (Ioi 0)) :
    Integrable f ∧ (∫ x, f x) = 2 * ∫ x in Ioi 0, f x := by
  have hl : IntegrableOn f (Iio 0) := by
    have hh := IntegrableOn.comp_neg_Iio (c := (0:ℝ)) (by simpa only [neg_zero] using hi)
    exact hh.congr_fun (fun x _ => he x) measurableSet_Iio
  have hlc : IntegrableOn f (Iic 0) := (integrableOn_Iic_iff_integrableOn_Iio (by finiteness)).mpr hl
  have hall : Integrable f := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0:ℝ)), integrableOn_union]
    exact ⟨hlc, hi⟩
  have hhalf : (∫ x in Iic 0, f x) = ∫ x in Ioi 0, f x := by
    rw [integral_Iic_eq_integral_Iio, ← integral_indicator measurableSet_Iio,
      ← integral_indicator measurableSet_Ioi]
    calc
      _ = ∫ x : ℝ, (Iio (0:ℝ)).indicator f (-x) := (integral_neg_eq_self _ volume).symm
      _ = _ := by
        congr 1
        funext x
        simp only [indicator, mem_Iio, mem_Ioi, neg_lt_zero, he]
  refine ⟨hall, ?_⟩
  have hh := intervalIntegral.integral_Iic_add_Ioi hlc hi
  rw [hhalf] at hh
  linarith

lemma t5_heavy_abs_moments (k : Fin 4) :
    Integrable (fun x : ℝ => |x|^(k:ℕ)) heavySix ∧
    (∫ x : ℝ, |x|^(k:ℕ) ∂heavySix) = ![(1:ℝ),1/4,1/6,1/4] k := by
  have he (x : ℝ) : t5_heavyDensity (-x) * |-x|^(k:ℕ) =
      t5_heavyDensity x * |x|^(k:ℕ) := by simp [t5_heavyDensity]
  have hh := t5_even_halves _ he (t5_heavy_positive_half k).1
  refine ⟨(t5_heavy_integrable_iff _).mpr hh.1, ?_⟩
  rw [t5_heavy_integral, hh.2, (t5_heavy_positive_half k).2]
  fin_cases k <;> norm_num

lemma t5_heavy_probability : IsProbabilityMeasure heavySix := by
  have hi := (t5_heavy_abs_moments 0).1
  have hm := (t5_heavy_abs_moments 0).2
  norm_num at hi hm
  have hf : IsFiniteMeasure heavySix := ⟨by
    simpa only [hasFiniteIntegral_iff_enorm, enorm_one, lintegral_one] using hi.hasFiniteIntegral⟩
  letI := hf
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top heavySix univ) (by simp)).mp
  simpa [measureReal_def] using hm

local instance t5_instHeavyProbability : IsProbabilityMeasure heavySix := t5_heavy_probability

lemma t5_heavy_mean : (∫ x : ℝ, x ∂heavySix) = 0 := by
  rw [t5_heavy_integral]
  have he : (fun x : ℝ => t5_heavyDensity (-x) * (-x)) =
      fun x => -(t5_heavyDensity x * x) := by
    funext x
    simp [t5_heavyDensity]
  have hh := integral_neg_eq_self (fun x : ℝ => t5_heavyDensity x*x) volume
  rw [he, integral_neg] at hh
  linarith

lemma t5_heavy_tail (R : ℝ) (hR : 0 ≤ R) :
    (heavySix (Ioi R)).toReal = 1/(2*(1+R)^5) ∧
    (heavySix (Iio (-R))).toReal = 1/(2*(1+R)^5) := by
  have hp : (∫ x in Ioi R, t5_heavyDensity x) = 1/(2*(1+R)^5) := by
    have he : t5_heavyDensity =ᵐ[volume.restrict (Ioi R)]
        (fun x : ℝ => (5/2)*(1/(1+x)^6)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [t5_heavyDensity, abs_of_nonneg (le_trans hR hx.out.le)]
      simp only [div_mul_eq_div_mul_one_div, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [integral_congr_ae he, integral_const_mul, (t5_shift_inv_integral 4 R hR).2]
    norm_num
    ring
  have hn : (∫ x in Iio (-R), t5_heavyDensity x) = ∫ x in Ioi R, t5_heavyDensity x := by
    rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi]
    calc
      _ = ∫ x : ℝ, (Iio (-R)).indicator t5_heavyDensity (-x) :=
        (integral_neg_eq_self _ volume).symm
      _ = _ := by
        congr 1
        funext x
        simp [indicator, t5_heavyDensity]
  have hmass (s : Set ℝ) (hs : MeasurableSet s) :
      (heavySix s).toReal = ∫ x in s, t5_heavyDensity x := by
    have hh := setIntegral_withDensity_eq_setIntegral_toReal_smul
      t5_heavyDensity_measurable.ennreal_ofReal (by simp)
      (fun _ : ℝ => (1:ℝ)) hs (μ := volume)
    simp only [integral_const, measureReal_def, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, smul_eq_mul, mul_one,
      ENNReal.toReal_ofReal (t5_heavyDensity_nonneg _)] at hh
    exact hh
  exact ⟨by rw [hmass _ measurableSet_Ioi, hp], by rw [hmass _ measurableSet_Iio, hn, hp]⟩

/-! Product and principal-stratum bookkeeping, with the actual fair assignment. -/

lemma t5_fair_probability : IsProbabilityMeasure fairAssignment := by
  constructor
  norm_num [fairAssignment, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]
  exact ENNReal.inv_two_add_inv_two

local instance t5_instFairProbability : IsProbabilityMeasure fairAssignment := t5_fair_probability

lemma t5_fair_singleton (a : Fin 2) : fairAssignment {a} = 1/2 := by
  fin_cases a <;> norm_num [fairAssignment, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply]

def t5_pair (a : Fin 2) (ω : State 2 0) : ℝ × Bool := (potentialY a ω, potentialS a ω)
def t5_joint (a : Fin 2) (ω : State 2 0) : (ℝ × Bool) × Fin 2 := (t5_pair a ω, assignment ω)
def t5_observables (ω : State 2 0) : (ℝ × Bool) × Fin 2 :=
  ((observedY ω, observedS ω), assignment ω)

@[fun_prop] lemma t5_pair_measurable (a : Fin 2) : Measurable (t5_pair a) := by
  unfold t5_pair
  fun_prop
@[fun_prop] lemma t5_joint_measurable (a : Fin 2) : Measurable (t5_joint a) := by
  unfold t5_joint
  fun_prop
@[fun_prop] lemma t5_observables_measurable : Measurable t5_observables := by
  unfold t5_observables
  fun_prop

@[fun_prop] lemma t5_stratum_measurable (s₁ s₂ : Bool) :
    Measurable (fun ω : (ℝ × ℝ) × Fin 2 =>
      ((![ω.1.1,ω.1.2], ![s₁,s₂], ω.2, fun _ => 0) : State 2 0)) := by
  refine Measurable.prodMk ?_ (measurable_const.prodMk (measurable_snd.prodMk measurable_const))
  exact measurable_pi_iff.mpr (fun i => by fin_cases i <;> fun_prop)

@[fun_prop] lemma t5_diagonal_measurable (s : Bool) :
    Measurable (fun ω : ℝ × Fin 2 =>
      ((![ω.1,ω.1], ![s,s], ω.2, fun _ => 0) : State 2 0)) := by
  refine Measurable.prodMk ?_ (measurable_const.prodMk (measurable_snd.prodMk measurable_const))
  exact measurable_pi_iff.mpr (fun i => by fin_cases i <;> fun_prop)

lemma t5_stratum_probability (s₁ s₂ : Bool) (F G : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G] :
    IsProbabilityMeasure (stratumLaw s₁ s₂ F G) := by
  unfold stratumLaw
  infer_instance

lemma t5_diagonal_probability (s : Bool) (F : Measure ℝ) [IsProbabilityMeasure F] :
    IsProbabilityMeasure (diagonalLaw s F) := by
  unfold diagonalLaw
  infer_instance

lemma t5_stratum_joint (s₁ s₂ : Bool) (F G : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G] (a : Fin 2) :
    (stratumLaw s₁ s₂ F G).map (t5_joint a) =
      (if a = 0 then F.map (fun y => (y,s₁)) else G.map (fun y => (y,s₂))).prod fairAssignment := by
  rw [stratumLaw, Measure.map_map (t5_joint_measurable a) (t5_stratum_measurable _ _)]
  fin_cases a
  · norm_num only [Fin.mk_zero, Fin.isValue, ite_true] at *
    change (((F.prod G).prod fairAssignment).map (fun ω => ((ω.1.1,s₁),ω.2))) = _
    have hp : (F.prod G).map (fun ω => (ω.1,s₁)) = F.map (fun y => (y,s₁)) := by
      calc
        _ = ((F.prod G).map Prod.fst).map (fun y => (y,s₁)) :=
          (Measure.map_map (by fun_prop) measurable_fst).symm
        _ = _ := by rw [Measure.map_fst_prod, measure_univ, one_smul]
    simpa only [Measure.map_id, hp, Prod.map_def, id_eq] using
      (Measure.map_prod_map (F.prod G) fairAssignment
        (show Measurable (fun ω : ℝ × ℝ => (ω.1,s₁)) by fun_prop) measurable_id).symm
  · norm_num only [Fin.isValue, Fin.mk_one, Fin.reduceEq, ite_false] at *
    change (((F.prod G).prod fairAssignment).map (fun ω => ((ω.1.2,s₂),ω.2))) = _
    have hp : (F.prod G).map (fun ω => (ω.2,s₂)) = G.map (fun y => (y,s₂)) := by
      calc
        _ = ((F.prod G).map Prod.snd).map (fun y => (y,s₂)) :=
          (Measure.map_map (by fun_prop) measurable_snd).symm
        _ = _ := by rw [Measure.map_snd_prod, measure_univ, one_smul]
    simpa only [Measure.map_id, hp, Prod.map_def, id_eq] using
      (Measure.map_prod_map (F.prod G) fairAssignment
        (show Measurable (fun ω : ℝ × ℝ => (ω.2,s₂)) by fun_prop) measurable_id).symm

lemma t5_diagonal_joint (s : Bool) (F : Measure ℝ) [IsProbabilityMeasure F] (a : Fin 2) :
    (diagonalLaw s F).map (t5_joint a) = (F.map (fun y => (y,s))).prod fairAssignment := by
  rw [diagonalLaw, Measure.map_map (t5_joint_measurable a) (t5_diagonal_measurable _)]
  have he : (fun ω : ℝ × Fin 2 => t5_joint a
      (![ω.1,ω.1], ![s,s], ω.2, fun _ => 0)) = fun ω => ((ω.1,s),ω.2) := by
    funext ω
    fin_cases a <;> rfl
  simp only [Function.comp_def, he]
  simpa only [Measure.map_id, Prod.map_def, id_eq] using
    (Measure.map_prod_map F fairAssignment
      (show Measurable (fun y : ℝ => (y,s)) by fun_prop) measurable_id).symm

lemma t5_stratum_always (s₁ s₂ : Bool) (F G : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G] :
    (stratumLaw s₁ s₂ F G).restrict alwaysPass =
      if s₁ = true ∧ s₂ = true then stratumLaw s₁ s₂ F G else 0 := by
  rw [stratumLaw, Measure.restrict_map (t5_stratum_measurable _ _) measurableSet_always]
  have he : (fun ω : (ℝ × ℝ) × Fin 2 =>
      ((![ω.1.1,ω.1.2], ![s₁,s₂], ω.2, fun _ => 0) : State 2 0)) ⁻¹' alwaysPass =
      if s₁ = true ∧ s₂ = true then univ else ∅ := by
    ext ω
    simp only [mem_preimage, alwaysPass, mem_setOf_eq, potentialS]
    cases s₁ <;> cases s₂ <;> simp [Fin.forall_fin_two]
  rw [he]
  split <;> simp_all [stratumLaw]

lemma t5_diagonal_always (s : Bool) (F : Measure ℝ) [IsProbabilityMeasure F] :
    (diagonalLaw s F).restrict alwaysPass = if s = true then diagonalLaw s F else 0 := by
  rw [diagonalLaw, Measure.restrict_map (t5_diagonal_measurable _) measurableSet_always]
  have he : (fun ω : ℝ × Fin 2 =>
      ((![ω.1,ω.1], ![s,s], ω.2, fun _ => 0) : State 2 0)) ⁻¹' alwaysPass =
      if s = true then univ else ∅ := by
    ext ω
    cases s <;> simp [alwaysPass, potentialS, Fin.forall_fin_two]
  rw [he]
  split <;> simp_all [diagonalLaw]

local instance t5_instStratumProbability (s₁ s₂ : Bool) (F G : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G] :
    IsProbabilityMeasure (stratumLaw s₁ s₂ F G) := t5_stratum_probability _ _ _ _

local instance t5_instDiagonalProbability (s : Bool) (F : Measure ℝ)
    [IsProbabilityMeasure F] : IsProbabilityMeasure (diagonalLaw s F) :=
  t5_diagonal_probability _ _

def t5_marginal : Measure (ℝ × Bool) :=
  (1/3:ℝ≥0∞) • beta33.map (fun y => (y,true)) +
  (2/3:ℝ≥0∞) • heavySix.map (fun y => (y,false))

lemma t5_marginal_probability : IsProbabilityMeasure t5_marginal := by
  constructor
  simp only [t5_marginal, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.div_add_div_same, show (1+2:ℝ≥0∞) = 3 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

local instance t5_instMarginalProbability : IsProbabilityMeasure t5_marginal := t5_marginal_probability

lemma t5_bounded_joint (a : Fin 2) :
    boundedPassLaw.map (t5_joint a) = t5_marginal.prod fairAssignment := by
  rw [boundedPassLaw, Measure.map_add _ _ (t5_joint_measurable a),
    Measure.map_smul _ (t5_joint_measurable a).aemeasurable,
    Measure.map_smul _ (t5_joint_measurable a).aemeasurable, t5_diagonal_joint, t5_diagonal_joint]
  rw [t5_marginal, Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left]

lemma t5_joint_pair {μ : Measure (State 2 0)} {L : Measure (ℝ × Bool)}
    [IsProbabilityMeasure L] (a : Fin 2)
    (h : μ.map (t5_joint a) = L.prod fairAssignment) :
    μ.map (t5_pair a) = L ∧ μ.map assignment = fairAssignment := by
  have hf := congrArg (Measure.map Prod.fst) h
  have hg := congrArg (Measure.map Prod.snd) h
  rw [Measure.map_map measurable_fst (t5_joint_measurable a),
    Measure.map_fst_prod, measure_univ, one_smul] at hf
  rw [Measure.map_map measurable_snd (t5_joint_measurable a),
    Measure.map_snd_prod, measure_univ, one_smul] at hg
  exact ⟨hf, hg⟩

lemma t5_joint_probability {μ : Measure (State 2 0)}
    (h : μ.map (t5_joint 0) = t5_marginal.prod fairAssignment) : IsProbabilityMeasure μ := by
  haveI : IsProbabilityMeasure (μ.map (t5_joint 0)) := h.symm ▸ inferInstance
  exact Measure.isProbabilityMeasure_of_map (t5_joint_measurable 0).aemeasurable

lemma t5_joint_assumptions {μ : Measure (State 2 0)}
    (h : ∀ a, μ.map (t5_joint a) = t5_marginal.prod fairAssignment) :
    Assumptions μ ∧ (∀ a, passingRate μ a = 1/3 ∧ trimRatio μ a = 2) := by
  letI := t5_joint_probability (h 0)
  have hpair (a) := t5_joint_pair a (h a)
  have hz (a : Fin 2) : μ (armEvent a) = 1/2 := by
    rw [← t5_fair_singleton a, ← (hpair a).2,
      Measure.map_apply measurable_assignment (measurableSet_singleton a)]
    rfl
  have hp (a : Fin 2) : μ (passEvent ∩ armEvent a) = 1/6 := by
    rw [pass_inter_arm]
    have hm := congrArg (fun ν : Measure ((ℝ × Bool) × Fin 2) =>
      ν ((univ ×ˢ {true}) ×ˢ {a})) (h a)
    rw [Measure.map_apply (t5_joint_measurable a)
      ((MeasurableSet.univ.prod (measurableSet_singleton true)).prod (measurableSet_singleton a)),
      Measure.prod_prod, t5_fair_singleton] at hm
    have he : t5_joint a ⁻¹' ((univ ×ˢ {true}) ×ˢ {a}) = potentialPass a ∩ armEvent a := by
      ext ω
      simp [t5_joint, t5_pair, potentialPass, armEvent]
    rw [he] at hm
    rw [hm]
    rw [t5_marginal, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.map_apply (by fun_prop : Measurable (fun y : ℝ => (y,true)))
        (MeasurableSet.univ.prod (measurableSet_singleton true)),
      Measure.map_apply (by fun_prop : Measurable (fun y : ℝ => (y,false)))
        (MeasurableSet.univ.prod (measurableSet_singleton true))]
    simp only [Set.preimage, mem_prod, mem_singleton_iff, mem_univ, true_and,
      Bool.false_eq_true, Set.setOf_true, Set.setOf_false, measure_univ, measure_empty,
      smul_eq_mul, mul_one, mul_zero, add_zero]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul]

  have hr (a : Fin 2) : passingRate μ a = 1/3 := by
    rw [passingRate, hp, hz]
    norm_num
  refine ⟨⟨inferInstance, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro a
    apply (indepFun_iff_map_prod_eq_prod_map_map
      (t5_pair_measurable a).aemeasurable measurable_assignment.aemeasurable).mpr
    change μ.map (t5_joint a) = _
    rw [h a, (hpair a).1, (hpair a).2]
  · intro a
    rw [hz]
    norm_num
  · intro a
    rw [hr]
    norm_num
  · intro a
    refine ⟨hr a, ?_⟩
    fin_cases a <;> norm_num [trimRatio, Fin.sum_univ_two, hr]

lemma t5_observables_partition (μ : Measure (State 2 0)) :
    μ.map t5_observables =
      (μ.map (t5_joint 0)).restrict {p | p.2 = 0} +
      (μ.map (t5_joint 1)).restrict {p | p.2 = 1} := by
  have hcomp : (armEvent (d := 0) (0:Fin 2))ᶜ = armEvent 1 := by
    ext ω
    change (¬ assignment ω = 0) ↔ assignment ω = 1
    generalize assignment ω = z
    fin_cases z <;> decide
  have hs (a : Fin 2) :
      (μ.restrict (armEvent a)).map t5_observables =
        (μ.map (t5_joint a)).restrict {p | p.2 = a} := by
    rw [Measure.restrict_map (t5_joint_measurable a)
      (show MeasurableSet {p : (ℝ × Bool) × Fin 2 | p.2 = a} from
        measurable_snd (measurableSet_singleton a))]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem (measurableSet_arm a)] with ω hω
    have hz : assignment ω = a := hω
    simp [t5_observables, t5_joint, t5_pair, observedY, observedS, hz]
  have hsplit := Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_arm (d := 0) (0:Fin 2))
  rw [hcomp] at hsplit
  conv_lhs => rw [← hsplit]
  rw [Measure.map_add _ _ t5_observables_measurable, hs 0, hs 1]

lemma t5_equal_observables {μ ν : Measure (State 2 0)}
    (h : ∀ a, μ.map (t5_joint a) = ν.map (t5_joint a)) :
    μ.map (fun ω => (observedY ω, observedS ω, assignment ω)) =
      ν.map (fun ω => (observedY ω, observedS ω, assignment ω)) := by
  have ho : μ.map t5_observables = ν.map t5_observables := by
    rw [t5_observables_partition μ, t5_observables_partition ν, h 0, h 1]
  have hh := congrArg (Measure.map (fun p : (ℝ × Bool) × Fin 2 => (p.1.1,p.1.2,p.2))) ho
  simpa only [Measure.map_map (show Measurable (fun p : (ℝ × Bool) × Fin 2 =>
      (p.1.1,p.1.2,p.2)) by fun_prop) t5_observables_measurable, Function.comp_def,
    t5_observables] using hh

/-! The beta tails, their normalized laws, and their recombination. -/

local instance t5_instBetaNull : NullSingletonClass beta33 := by
  unfold beta33
  infer_instance

lemma t5_beta_upper_partial (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (beta33 (Ioo (1-t) 1)).toReal = (beta33 (Ioo 0 t)).toReal ∧
    (∫ x in Ioo (1-t) 1, x ∂beta33) =
      (beta33 (Ioo 0 t)).toReal - ((15/2:ℝ)*t^4 - 12*t^5 + 5*t^6) := by
  have hsplit (n : ℕ) :
      (∫ x in Ioo (1-t) 1, x^n ∂beta33) =
        (∫ x in Ioo 0 1, x^n ∂beta33) - ∫ x in Ioo 0 (1-t), x^n ∂beta33 := by
    have hi := (t5_beta_integrable_continuous (show Continuous (fun x : ℝ => x^n) by fun_prop))
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (a := (0:ℝ)) (b := 1-t) (c := 1) (μ := beta33) hi.intervalIntegrable hi.intervalIntegrable
    rw [intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1-t),
      intervalIntegral.integral_of_le (by linarith : 1-t ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo] at hh
    linarith
  have h0 := hsplit 0
  have h1 := hsplit 1
  rw [t5_beta_partial 1 (by norm_num) (by norm_num),
    t5_beta_partial (1-t) (by linarith) (by linarith)] at h0 h1
  norm_num [integral_const, measureReal_def] at h0 h1
  rw [t5_beta_cdf t ht.le ht1.le]
  constructor <;> linarith [h0, h1]

lemma t5_beta_cdf_strict (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    0 < (beta33 (Ioo 0 t)).toReal ∧ (beta33 (Ioo 0 t)).toReal < 1 := by
  have hpos (s : ℝ) (hs : 0 < s) : 0 < 10*s^3 - 15*s^4 + 6*s^5 := by
    have hp : 0 < 10-15*s+6*s^2 := by nlinarith [sq_nonneg (s-5/4)]
    calc
      _ = s^3*(10-15*s+6*s^2) := by ring
      _ > 0 := mul_pos (pow_pos hs _) hp
  rw [t5_beta_cdf t ht.le ht1.le]
  refine ⟨hpos t ht, ?_⟩
  have hh := hpos (1-t) (by linarith)
  nlinarith

def t5_tailSet (t : ℝ) (upper : Bool) : Set ℝ := if upper then Ioo (1-t) 1 else Ioo 0 t

lemma t5_tailSet_measurable (t : ℝ) (upper : Bool) : MeasurableSet (t5_tailSet t upper) := by
  cases upper <;> exact measurableSet_Ioo

lemma t5_tailSet_subset (t : ℝ) (upper : Bool) (ht : 0 < t) (ht1 : t < 1) :
    t5_tailSet t upper ⊆ Ioo (0:ℝ) 1 := by
  cases upper <;> dsimp [t5_tailSet] <;> intro x hx <;> constructor <;> linarith [hx.1, hx.2]

lemma t5_tailSet_mass (t : ℝ) (upper : Bool) (ht : 0 < t) (ht1 : t < 1) :
    (beta33 (t5_tailSet t upper)).toReal = (beta33 (Ioo 0 t)).toReal := by
  cases upper
  · rfl
  · exact (t5_beta_upper_partial t ht ht1).1

lemma t5_conditional_id {μ : Measure ℝ} [IsProbabilityMeasure μ] {E : Set ℝ}
    (hE : MeasurableSet E) (hpos : 0 < μ E) :
    IsProbabilityMeasure (eventLaw μ id E) := by
  unfold eventLaw
  rw [Measure.map_id]
  constructor
  simp only [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' (measure_ne_top μ E)

lemma t5_beta_decomposition {E : Set ℝ} (hE : MeasurableSet E) (hsub : E ⊆ Ioo (0:ℝ) 1)
    (hq : 0 < (beta33 E).toReal) (hq1 : (beta33 E).toReal < 1) :
    IsProbabilityMeasure (eventLaw beta33 id E) ∧
    IsProbabilityMeasure (eventLaw beta33 id (Ioo 0 1 \ E)) ∧
    ENNReal.ofReal ((beta33 E).toReal) • eventLaw beta33 id E +
      ENNReal.ofReal (1-(beta33 E).toReal) • eventLaw beta33 id (Ioo 0 1 \ E) = beta33 := by
  have hr : beta33.restrict (Ioo (0:ℝ) 1) = beta33 := Measure.restrict_eq_self_of_ae_mem t5_beta_ae
  have hs : beta33.restrict E + beta33.restrict (Ioo 0 1 \ E) = beta33 := by
    rw [← Measure.restrict_union (disjoint_sdiff_right) (measurableSet_Ioo.diff hE),
      union_sdiff_cancel hsub, hr]
  have hc : (beta33 (Ioo 0 1 \ E)).toReal = 1-(beta33 E).toReal := by
    have hm := congrArg (fun ν : Measure ℝ => (ν univ).toReal) hs
    simp only [Measure.add_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      ENNReal.toReal_add (measure_ne_top beta33 _) (measure_ne_top beta33 _),
      measure_univ, ENNReal.toReal_one] at hm
    linarith
  have hpE : 0 < beta33 E := ENNReal.toReal_pos_iff.mp hq |>.1
  have hpC : 0 < beta33 (Ioo 0 1 \ E) :=
    (ENNReal.toReal_pos_iff.mp (by rw [hc]; linarith)).1
  refine ⟨t5_conditional_id hE hpE,
    t5_conditional_id (measurableSet_Ioo.diff hE) hpC, ?_⟩
  rw [← hc, ENNReal.ofReal_toReal (measure_ne_top beta33 _),
    ENNReal.ofReal_toReal (measure_ne_top beta33 _)]
  simp only [eventLaw, Measure.map_id, smul_smul,
    ENNReal.mul_inv_cancel hpE.ne' (measure_ne_top beta33 E),
    ENNReal.mul_inv_cancel hpC.ne' (measure_ne_top beta33 _), one_smul]
  exact hs

def t5_endpoint (E : Set ℝ) : Measure (State 2 0) :=
  let q := (beta33 E).toReal
  let F := eventLaw beta33 id E
  let G := eventLaw beta33 id (Ioo 0 1 \ E)
  ENNReal.ofReal (q/3) • stratumLaw true true F F +
  ENNReal.ofReal ((1-q)/3) • stratumLaw true false G heavySix +
  ENNReal.ofReal ((1-q)/3) • stratumLaw false true heavySix G +
  ENNReal.ofReal ((1+q)/3) • stratumLaw false false heavySix heavySix

lemma t5_endpoint_joint {E : Set ℝ} (hE : MeasurableSet E) (hsub : E ⊆ Ioo (0:ℝ) 1)
    (hq : 0 < (beta33 E).toReal) (hq1 : (beta33 E).toReal < 1) (a : Fin 2) :
    (t5_endpoint E).map (t5_joint a) = t5_marginal.prod fairAssignment := by
  obtain ⟨hF,hG,hFG⟩ := t5_beta_decomposition hE hsub hq hq1
  letI := hF
  letI := hG
  let q := (beta33 E).toReal
  let F := eventLaw beta33 id E
  let G := eventLaw beta33 id (Ioo 0 1 \ E)
  have hw0 : ENNReal.ofReal (q/3) = (1/3:ℝ≥0∞)*ENNReal.ofReal q := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 3)]
    norm_num [div_eq_mul_inv, mul_comm]
  have hw1 : ENNReal.ofReal ((1-q)/3) = (1/3:ℝ≥0∞)*ENNReal.ofReal (1-q) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 3)]
    norm_num [div_eq_mul_inv, mul_comm]
  have hws : ENNReal.ofReal ((1-q)/3) + ENNReal.ofReal ((1+q)/3) = (2/3:ℝ≥0∞) := by
    rw [← ENNReal.ofReal_add (by dsimp [q]; linarith) (by dsimp [q]; linarith)]
    rw [show (1-q)/3+(1+q)/3 = (2/3:ℝ) by ring]
    norm_num [ENNReal.ofReal_div_of_pos]
  have hm : ENNReal.ofReal (q/3) • F.map (fun y => (y,true)) +
      ENNReal.ofReal ((1-q)/3) • G.map (fun y => (y,true)) +
      ENNReal.ofReal ((1-q)/3) • heavySix.map (fun y => (y,false)) +
      ENNReal.ofReal ((1+q)/3) • heavySix.map (fun y => (y,false)) = t5_marginal := by
    have hg := congrArg (Measure.map (fun y : ℝ => (y,true))) hFG
    simp only [Measure.map_add _ _ (by fun_prop : Measurable (fun y : ℝ => (y,true))),
      Measure.map_smul _ (show Measurable (fun y : ℝ => (y,true)) by fun_prop).aemeasurable] at hg
    change ENNReal.ofReal q • F.map (fun y => (y,true)) +
      ENNReal.ofReal (1-q) • G.map (fun y => (y,true)) = beta33.map (fun y => (y,true)) at hg
    calc
      _ = (ENNReal.ofReal (q/3) • F.map (fun y => (y,true)) +
          ENNReal.ofReal ((1-q)/3) • G.map (fun y => (y,true))) +
          (ENNReal.ofReal ((1-q)/3)+ENNReal.ofReal ((1+q)/3)) •
            heavySix.map (fun y => (y,false)) := by module
      _ = (1/3:ℝ≥0∞) • (ENNReal.ofReal q • F.map (fun y => (y,true)) +
          ENNReal.ofReal (1-q) • G.map (fun y => (y,true))) +
          (2/3:ℝ≥0∞) • heavySix.map (fun y => (y,false)) := by
        rw [hws, hw0, hw1]
        module
      _ = _ := by rw [hg]; rfl
  simp only [t5_endpoint, Measure.map_add _ _ (t5_joint_measurable a),
    Measure.map_smul _ (t5_joint_measurable a).aemeasurable,
    t5_stratum_joint]
  fin_cases a <;> norm_num only [Fin.isValue, Fin.reduceEq, Fin.mk_zero, Fin.mk_one, ite_true, ite_false]
  all_goals simp only [← Measure.prod_smul_left, ← Measure.add_prod]
  all_goals apply congrArg (fun L : Measure (ℝ × Bool) => L.prod fairAssignment)
  · exact hm
  · calc
      _ = ENNReal.ofReal (q/3) • F.map (fun y => (y,true)) +
          ENNReal.ofReal ((1-q)/3) • G.map (fun y => (y,true)) +
          ENNReal.ofReal ((1-q)/3) • heavySix.map (fun y => (y,false)) +
          ENNReal.ofReal ((1+q)/3) • heavySix.map (fun y => (y,false)) := by module
      _ = _ := hm

lemma t5_stratum_potential (F : Measure ℝ) [IsProbabilityMeasure F] (a : Fin 2) :
    (stratumLaw true true F F).map (potentialY a) = F := by
  have hj : (stratumLaw true true F F).map (t5_joint a) =
      (F.map (fun y => (y,true))).prod fairAssignment := by
    simpa only [ite_self] using t5_stratum_joint true true F F a
  have hp := (t5_joint_pair a hj).1
  have hh := congrArg (Measure.map Prod.fst) hp
  rw [Measure.map_map measurable_fst (t5_pair_measurable a),
    Measure.map_map measurable_fst (by fun_prop : Measurable (fun y : ℝ => (y,true)))] at hh
  change (stratumLaw true true F F).map (potentialY a) = F.map id at hh
  simpa only [Measure.map_id] using hh

lemma t5_endpoint_always {E : Set ℝ} (hE : MeasurableSet E) (hsub : E ⊆ Ioo (0:ℝ) 1)
    (hq : 0 < (beta33 E).toReal) (hq1 : (beta33 E).toReal < 1) :
    (t5_endpoint E).restrict alwaysPass =
      ENNReal.ofReal ((beta33 E).toReal/3) •
        stratumLaw true true (eventLaw beta33 id E) (eventLaw beta33 id E) := by
  obtain ⟨hF,hG,_⟩ := t5_beta_decomposition hE hsub hq hq1
  letI := hF
  letI := hG
  simp [t5_endpoint, Measure.restrict_add, Measure.restrict_smul, t5_stratum_always]

lemma t5_endpoint_certificate {E : Set ℝ} (hE : MeasurableSet E) (hsub : E ⊆ Ioo (0:ℝ) 1)
    (hq : 0 < (beta33 E).toReal) (hq1 : (beta33 E).toReal < 1) :
    Compatible boundedPassLaw (t5_endpoint E) ∧
    ∀ a : Fin 2, eventMean (t5_endpoint E) (potentialY a) alwaysPass =
      (∫ x in E, x ∂beta33)/(beta33 E).toReal := by
  obtain ⟨hF,hG,_⟩ := t5_beta_decomposition hE hsub hq hq1
  letI := hF
  letI := hG
  have hj := t5_endpoint_joint hE hsub hq hq1
  have ha := (t5_joint_assumptions hj).1
  have hr := t5_endpoint_always hE hsub hq hq1
  have hmass : t5_endpoint E alwaysPass = ENNReal.ofReal ((beta33 E).toReal/3) := by
    have hh := congrArg (fun ν : Measure (State 2 0) => ν univ) hr
    simpa using hh
  refine ⟨⟨ha, ?_, ?_⟩, ?_⟩
  · rw [hmass]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  · exact t5_equal_observables (fun a => (hj a).trans (t5_bounded_joint a).symm)
  · intro a
    rw [eventMean, hr, integral_smul_measure, hmass]
    have hi : (∫ ω, potentialY a ω ∂stratumLaw true true (eventLaw beta33 id E)
        (eventLaw beta33 id E)) = ∫ x, x ∂eventLaw beta33 id E := by
      calc
        _ = ∫ x, id x ∂(stratumLaw true true (eventLaw beta33 id E)
            (eventLaw beta33 id E)).map (potentialY a) :=
          (integral_map (measurable_potentialY a).aemeasurable measurable_id.aestronglyMeasurable).symm
        _ = _ := by rw [t5_stratum_potential]; rfl
    rw [hi, eventLaw, Measure.map_id, integral_smul_measure]
    simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (beta33 E).toReal/3),
      ENNReal.toReal_inv, smul_eq_mul]
    field_simp

/-! Properties of the baseline distribution. -/

lemma t5_diagonal_observed (s : Bool) (F : Measure ℝ) [IsProbabilityMeasure F] :
    (diagonalLaw s F).map (fun ω => (observedY ω, observedS ω)) =
      F.map (fun y => (y,s)) := by
  rw [diagonalLaw, Measure.map_map (by fun_prop) (t5_diagonal_measurable s)]
  have he : (fun ω : ℝ × Fin 2 =>
      (observedY ((![ω.1,ω.1], ![s,s], ω.2, fun _ => 0) : State 2 0),
       observedS ((![ω.1,ω.1], ![s,s], ω.2, fun _ => 0) : State 2 0))) = fun ω => (ω.1,s) := by
    funext ω
    rcases ω with ⟨y,z⟩
    fin_cases z <;> rfl
  simp only [Function.comp_def, he]
  calc
    _ = ((F.prod fairAssignment).map Prod.fst).map (fun y => (y,s)) :=
      (Measure.map_map (by fun_prop) measurable_fst).symm
    _ = _ := by rw [Measure.map_fst_prod, measure_univ, one_smul]

lemma t5_bounded_obsPair :
    boundedPassLaw.map (fun ω => (observedY ω, observedS ω)) = t5_marginal := by
  simp only [boundedPassLaw, Measure.map_add _ _ (by fun_prop :
      Measurable (fun ω : State 2 0 => (observedY ω, observedS ω))),
    Measure.map_smul _ (show Measurable (fun ω : State 2 0 => (observedY ω, observedS ω)) by fun_prop).aemeasurable,
    t5_diagonal_observed]
  rfl

lemma t5_bounded_obsY :
    boundedPassLaw.map observedY = (1/3:ℝ≥0∞) • beta33 + (2/3:ℝ≥0∞) • heavySix := by
  have hh := congrArg (Measure.map Prod.fst) t5_bounded_obsPair
  rw [Measure.map_map measurable_fst (by fun_prop)] at hh
  simp only [t5_marginal, Measure.map_add _ _ measurable_fst,
    Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_map measurable_fst (by fun_prop : Measurable (fun y : ℝ => (y,true))),
    Measure.map_map measurable_fst (by fun_prop : Measurable (fun y : ℝ => (y,false))),
    Function.comp_def] at hh
  change boundedPassLaw.map observedY = (1/3:ℝ≥0∞) • beta33.map id +
    (2/3:ℝ≥0∞) • heavySix.map id at hh
  simpa only [Measure.map_id] using hh

local instance t5_instBoundedProbability : IsProbabilityMeasure boundedPassLaw :=
  t5_joint_probability (t5_bounded_joint 0)

lemma t5_bounded_always : boundedPassLaw alwaysPass = 1/3 := by
  have hr : boundedPassLaw.restrict alwaysPass = (1/3:ℝ≥0∞) • diagonalLaw true beta33 := by
    simp [boundedPassLaw, Measure.restrict_add, Measure.restrict_smul, t5_diagonal_always]
  have hh := congrArg (fun ν : Measure (State 2 0) => ν univ) hr
  simpa using hh

lemma t5_bounded_integral (g : ℝ → ℝ) (hg : Measurable g)
    (hb : Integrable g beta33) (hh : Integrable g heavySix) :
    Integrable (fun ω => g (observedY ω)) boundedPassLaw ∧
    (∫ ω, g (observedY ω) ∂boundedPassLaw) =
      (1/3:ℝ)*(∫ x, g x ∂beta33)+(2/3:ℝ)*(∫ x, g x ∂heavySix) := by
  have hi : Integrable g (boundedPassLaw.map observedY) := by
    rw [t5_bounded_obsY]
    exact (hb.smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))).add_measure (hh.smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num)))
  refine ⟨(integrable_map_measure hg.aestronglyMeasurable measurable_observedY.aemeasurable).mp hi, ?_⟩
  rw [← integral_map measurable_observedY.aemeasurable hg.aestronglyMeasurable,
    t5_bounded_obsY, integral_add_measure (hb.smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num)))
      (hh.smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))), integral_smul_measure, integral_smul_measure]
  norm_num

lemma t5_bounded_moments :
    (∫ ω, observedY ω ∂boundedPassLaw) = 1/6 ∧
    (∫ ω, observedY ω^2 ∂boundedPassLaw) = 13/63 ∧
    (∫ ω, |observedY ω|^3 ∂boundedPassLaw) = 19/84 ∧
    Integrable (fun ω => |observedY ω|^3) boundedPassLaw := by
  have hiAbs : Integrable (fun x : ℝ => |x|) heavySix := by
    simpa using! (t5_heavy_abs_moments 1).1
  have hiH : Integrable (fun x : ℝ => x) heavySix :=
    (integrable_norm_iff measurable_id.aestronglyMeasurable).mp hiAbs
  have hiH2 : Integrable (fun x : ℝ => x^2) heavySix := by
    simpa using! (t5_heavy_abs_moments 2).1
  have hmH2 : (∫ x : ℝ, x^2 ∂heavySix) = 1/6 := by
    simpa using! (t5_heavy_abs_moments 2).2
  have hiH3 : Integrable (fun x : ℝ => |x|^3) heavySix := by
    simpa using! (t5_heavy_abs_moments 3).1
  have hmH3 : (∫ x : ℝ, |x|^3 ∂heavySix) = 1/4 := by
    simpa using! (t5_heavy_abs_moments 3).2
  have h1 := t5_bounded_integral (fun x : ℝ => x) measurable_id
    (t5_beta_integrable_continuous continuous_id) hiH
  have h2 := t5_bounded_integral (fun x => x^2) (by fun_prop)
    (t5_beta_integrable_continuous (by fun_prop)) hiH2
  have h3 := t5_bounded_integral (fun x => |x|^3) (by fun_prop)
    (t5_beta_integrable_continuous (by fun_prop)) hiH3
  rw [t5_beta_moments.1, t5_heavy_mean] at h1
  rw [t5_beta_moments.2.1, hmH2] at h2
  rw [t5_beta_moments.2.2, hmH3] at h3
  norm_num at h1 h2 h3
  exact ⟨h1.2, h2.2, h3.2, h3.1⟩

lemma t5_bounded_atomless : Atomless (boundedPassLaw.map observedY) := by
  intro x
  rw [t5_bounded_obsY]
  simp only [Measure.add_apply, Measure.smul_apply]
  have hb : beta33 {x} = 0 := measure_singleton x
  have hh : heavySix {x} = 0 := by unfold heavySix; exact measure_singleton x
  simp [hb, hh]

lemma t5_heavy_fullsupport (l u : ℝ) (hlu : l < u) : 0 < heavySix (Ioo l u) := by
  have hac : (volume : Measure ℝ) ≪ heavySix :=
    withDensity_absolutelyContinuous' t5_heavyDensity_measurable.ennreal_ofReal.aemeasurable
      (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (by
        positivity)).ne')
  apply pos_iff_ne_zero.mpr
  intro hz
  have hv := hac hz
  have hp : 0 < volume (Ioo l u) := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hlu)
  exact hp.ne' hv

lemma t5_bounded_fullsupport : FullRealSupport boundedPassLaw observedY := by
  intro l u hlu
  have hm := Measure.map_apply measurable_observedY measurableSet_Ioo (μ := boundedPassLaw)
    (s := Ioo l u)
  change (boundedPassLaw.map observedY) (Ioo l u) = boundedPassLaw {ω | l < observedY ω ∧ observedY ω < u} at hm
  rw [← hm, t5_bounded_obsY, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  exact lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨by norm_num, t5_heavy_fullsupport l u hlu⟩)
    (le_add_left le_rfl)

lemma t5_bounded_tails (R : ℝ) (hR : 1 ≤ R) :
    (boundedPassLaw {ω | R < observedY ω}).toReal = 1/(3*(1+R)^5) ∧
    (boundedPassLaw {ω | observedY ω < -R}).toReal = 1/(3*(1+R)^5) := by
  have hb1 : beta33 (Ioi R) = 0 := by
    apply measure_mono_null (show Ioi R ⊆ (Ioo (0:ℝ) 1)ᶜ by intro x hx; simp only [mem_compl_iff, mem_Ioo]; intro h; linarith [hx.out, h.2])
    exact ae_iff.mp t5_beta_ae
  have hb2 : beta33 (Iio (-R)) = 0 := by
    apply measure_mono_null (show Iio (-R) ⊆ (Ioo (0:ℝ) 1)ᶜ by intro x hx; simp only [mem_compl_iff, mem_Ioo]; intro h; linarith [hx.out, h.1])
    exact ae_iff.mp t5_beta_ae
  have hp := t5_heavy_tail R (by linarith)
  have hm1 := Measure.map_apply measurable_observedY measurableSet_Ioi (μ := boundedPassLaw) (s := Ioi R)
  have hm2 := Measure.map_apply measurable_observedY measurableSet_Iio (μ := boundedPassLaw) (s := Iio (-R))
  change _ = boundedPassLaw {ω | R < observedY ω} at hm1
  change _ = boundedPassLaw {ω | observedY ω < -R} at hm2
  rw [← hm1, ← hm2, t5_bounded_obsY]
  simp only [Measure.add_apply, Measure.smul_apply, hb1, hb2, smul_eq_mul,
    mul_zero, zero_add, ENNReal.toReal_mul, hp.1, hp.2]
  norm_num <;> ring
lemma t5_strict_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (E : Set Ω) (hE : MeasurableSet E)
    (hmass : 0 < μ E) (u : ℝ) (hu : 0 < u)
    (hs : ∀ᵐ ω ∂μ.restrict E, 0 < f ω ∧ f ω < u) :
    0 < eventMean μ f E ∧ eventMean μ f E < u := by
  have hi : Integrable f (μ.restrict E) :=
    (integrable_const u).mono' hf.aestronglyMeasurable (hs.mono fun ω hω => by
      simpa only [Real.norm_eq_abs, abs_of_pos hω.1] using hω.2.le)
  have hp (g : Ω → ℝ) (hg : Integrable g (μ.restrict E))
      (hpos : ∀ᵐ ω ∂μ.restrict E, 0 < g ω) : 0 < ∫ ω in E, g ω ∂μ := by
    apply (integral_pos_iff_support_of_nonneg_ae (hpos.mono fun _ h => h.le) hg).mpr
    have he : Function.support g =ᵐ[μ.restrict E] (univ : Set Ω) := by
      filter_upwards [hpos] with ω hω
      simp [hω.ne']
    rw [measure_congr he, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact hmass
  have hp0 := hp f hi (hs.mono fun _ h => h.1)
  have hp1 := hp (fun ω => u-f ω) ((integrable_const u).sub' hi)
    (hs.mono fun _ h => sub_pos.mpr h.2)
  have hm : 0 < (μ E).toReal := ENNReal.toReal_pos hmass.ne' (measure_ne_top μ E)
  rw [integral_sub (integrable_const u) hi, integral_const] at hp1
  simp only [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    smul_eq_mul] at hp1
  exact ⟨div_pos hp0 hm, (div_lt_iff₀ hm).mpr (by nlinarith)⟩

lemma t5_endpoint_tail_data (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (∀ upper : Bool, Compatible boundedPassLaw (betaEndpointLaw t upper)) ∧
    ∀ a : Fin 2,
      eventMean (betaEndpointLaw t false) (potentialY a) alwaysPass =
        t*(15/2-12*t+5*t^2)/(10-15*t+6*t^2) ∧
      0 < eventMean (betaEndpointLaw t false) (potentialY a) alwaysPass ∧
      eventMean (betaEndpointLaw t false) (potentialY a) alwaysPass < t ∧
      eventMean (betaEndpointLaw t true) (potentialY a) alwaysPass =
        1-eventMean (betaEndpointLaw t false) (potentialY a) alwaysPass := by
  have hq := t5_beta_cdf_strict t ht ht1
  have hcert (upper : Bool) := t5_endpoint_certificate (t5_tailSet_measurable t upper)
    (t5_tailSet_subset t upper ht ht1)
    (by rw [t5_tailSet_mass t upper ht ht1]; exact hq.1)
    (by rw [t5_tailSet_mass t upper ht ht1]; exact hq.2)
  have hsame (upper : Bool) : betaEndpointLaw t upper = t5_endpoint (t5_tailSet t upper) := rfl
  have hlower (a : Fin 2) : eventMean (betaEndpointLaw t false) (potentialY a) alwaysPass =
      ((15/2:ℝ)*t^4-12*t^5+5*t^6)/(beta33 (Ioo 0 t)).toReal := by
    rw [hsame, (hcert false).2 a]
    have h := t5_beta_partial t ht.le ht1.le 1
    norm_num at h
    dsimp [t5_tailSet]
    rw [h]
    ring
  have hM : (∫ x in Ioo 0 t, x ∂beta33) = (15/2:ℝ)*t^4-12*t^5+5*t^6 := by
    rw [show (fun x : ℝ => x) = (fun x => x^1) by simp,
      t5_beta_partial t ht.le ht1.le 1]
    norm_num <;> ring
  have hsmean := t5_strict_mean beta33 id measurable_id (Ioo 0 t) measurableSet_Ioo
    (ENNReal.toReal_pos_iff.mp hq.1 |>.1) t ht
    (ae_restrict_mem measurableSet_Ioo)
  have hsmean' : 0 < ((15/2:ℝ)*t^4-12*t^5+5*t^6)/(beta33 (Ioo 0 t)).toReal ∧
      ((15/2:ℝ)*t^4-12*t^5+5*t^6)/(beta33 (Ioo 0 t)).toReal < t := by
    simpa only [eventMean, id_eq, hM] using hsmean
  have hden : 0 < 10-15*t+6*t^2 := by nlinarith [sq_nonneg (t-5/4)]
  refine ⟨fun upper => by rw [hsame]; exact (hcert upper).1, ?_⟩
  intro a
  refine ⟨?_, by rw [hlower]; exact hsmean'.1, by rw [hlower]; exact hsmean'.2, ?_⟩
  · rw [hlower, t5_beta_cdf t ht.le ht1.le]
    have hfac : 10*t^3-15*t^4+6*t^5 = t^3*(10-15*t+6*t^2) := by ring
    rw [hfac]
    field_simp <;> ring
  · rw [hsame true, (hcert true).2 a, hlower]
    change (∫ x in Ioo (1-t) 1, x ∂beta33)/(beta33 (Ioo (1-t) 1)).toReal = _
    rw [(t5_beta_upper_partial t ht ht1).1, (t5_beta_upper_partial t ht ht1).2]
    field_simp [hq.1.ne'] <;> ring

/-! Strict bounds for every compatible law, using only per-arm ignorability. -/

def t5_bad : Set (ℝ × Bool) := (Ioo (0:ℝ) 1)ᶜ ×ˢ {true}

lemma t5_bad_measurable : MeasurableSet t5_bad :=
  measurableSet_Ioo.compl.prod (measurableSet_singleton true)

lemma t5_marginal_bad : t5_marginal t5_bad = 0 := by
  have hb : beta33 (Ioo (0:ℝ) 1)ᶜ = 0 := ae_iff.mp t5_beta_ae
  have ht : (fun y : ℝ => (y,true)) ⁻¹' t5_bad = (Ioo (0:ℝ) 1)ᶜ := by
    ext y
    simp [t5_bad]
  have hf : (fun y : ℝ => (y,false)) ⁻¹' t5_bad = ∅ := by
    ext y
    simp [t5_bad]
  rw [t5_marginal, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (by fun_prop) t5_bad_measurable,
    Measure.map_apply (by fun_prop) t5_bad_measurable, ht, hf, hb]
  simp

lemma t5_compatible_obsPair {ν : Measure (State 2 0)} (hc : Compatible boundedPassLaw ν) :
    ν.map (fun ω => (observedY ω, observedS ω)) = t5_marginal := by
  have hh := congrArg (Measure.map (fun p : ℝ × Bool × Fin 2 => (p.1,p.2.1))) hc.2.2
  have hm : Measurable (fun p : ℝ × Bool × Fin 2 => (p.1,p.2.1)) := by fun_prop
  simp only [Measure.map_map hm (by fun_prop : Measurable
    (fun ω : State 2 0 => (observedY ω, observedS ω, assignment ω))), Function.comp_def] at hh
  exact hh.trans t5_bounded_obsPair

lemma t5_compatible_support {ν : Measure (State 2 0)} (hc : Compatible boundedPassLaw ν)
    (a : Fin 2) : ∀ᵐ ω ∂ν.restrict alwaysPass, 0 < potentialY a ω ∧ potentialY a ω < 1 := by
  letI := hc.1.1
  have hnull : ν ((fun ω => (observedY ω,observedS ω)) ⁻¹' t5_bad) = 0 := by
    rw [← Measure.map_apply (by fun_prop) t5_bad_measurable,
      t5_compatible_obsPair hc, t5_marginal_bad]
  have hind := (hc.1.2.1.1 a).measure_inter_preimage_eq_mul t5_bad {a}
    t5_bad_measurable (measurableSet_singleton a)
  change ν (t5_pair a ⁻¹' t5_bad ∩ armEvent a) =
    ν (t5_pair a ⁻¹' t5_bad)*ν (armEvent a) at hind
  have hz : ν (t5_pair a ⁻¹' t5_bad ∩ armEvent a) = 0 := by
    apply measure_mono_null _ hnull
    intro ω hω
    have hza : assignment ω = a := hω.2
    simpa only [mem_preimage, observedY, observedS, hza, t5_pair] using hω.1
  have hn : ν (t5_pair a ⁻¹' t5_bad) = 0 :=
    (mul_eq_zero.mp (hind.symm.trans hz)).resolve_right (hc.1.2.1.2 a).ne'
  have hgood : ∀ᵐ ω ∂ν, ω ∉ t5_pair a ⁻¹' t5_bad := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hn
  rw [ae_restrict_iff' measurableSet_always]
  filter_upwards [hgood] with ω hω hA
  change (∀ b, potentialS b ω = true) at hA
  have hy : potentialY a ω ∈ Ioo (0:ℝ) 1 := by
    by_contra hnot
    apply hω
    exact ⟨hnot, hA a⟩
  exact hy

lemma t5_compatible_mean (a : Fin 2) :
    ∀ m ∈ identifiedMeans boundedPassLaw a, 0 < m ∧ m < 1 := by
  rintro m ⟨ν,hc,rfl⟩
  letI := hc.1.1
  exact t5_strict_mean ν (potentialY a) (measurable_potentialY a) alwaysPass
    measurableSet_always hc.2.1 1 (by norm_num) (t5_compatible_support hc a)

lemma t5_extrema (a : Fin 2) :
    IsGLB (extendedMeans boundedPassLaw a) 0 ∧ IsLUB (extendedMeans boundedPassLaw a) 1 ∧
    ¬ IsGLB (extendedMeans boundedPassLaw a) ⊥ ∧ ¬ IsLUB (extendedMeans boundedPassLaw a) ⊤ := by
  have hm (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (upper : Bool) :
      (eventMean (betaEndpointLaw t upper) (potentialY a) alwaysPass : EReal) ∈
        extendedMeans boundedPassLaw a :=
    ⟨_, ⟨betaEndpointLaw t upper, (t5_endpoint_tail_data t ht ht1).1 upper, rfl⟩, rfl⟩
  have hg : IsGLB (extendedMeans boundedPassLaw a) 0 := by
    refine ⟨?_, ?_⟩
    · rintro x ⟨m,hm,rfl⟩
      exact_mod_cast (t5_compatible_mean a m hm).1.le
    · intro b hb
      by_contra h
      obtain ⟨r,hr0,hrb⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
      have hr : 0 < r := by exact_mod_cast hr0
      let t := min r (1/2:ℝ)
      have ht : 0 < t := lt_min hr (by norm_num)
      have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hd := (t5_endpoint_tail_data t ht ht1).2 a
      have hlt : (eventMean (betaEndpointLaw t false) (potentialY a) alwaysPass : EReal) < b :=
        lt_trans (EReal.coe_lt_coe_iff.mpr (lt_of_lt_of_le hd.2.2.1 (min_le_left _ _))) hrb
      exact (not_lt_of_ge (hb (hm t ht ht1 false))) hlt
  have hu : IsLUB (extendedMeans boundedPassLaw a) 1 := by
    refine ⟨?_, ?_⟩
    · rintro x ⟨m,hm,rfl⟩
      exact_mod_cast (t5_compatible_mean a m hm).2.le
    · intro b hb
      by_contra h
      obtain ⟨r,hbr,hr1⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
      have hr : r < 1 := by exact_mod_cast hr1
      let t := min (1-r) (1/2:ℝ)
      have ht : 0 < t := lt_min (by linarith) (by norm_num)
      have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hd := (t5_endpoint_tail_data t ht ht1).2 a
      have hgt : r < eventMean (betaEndpointLaw t true) (potentialY a) alwaysPass := by
        rw [hd.2.2.2]
        have hl := hd.2.2.1
        have htt : t ≤ 1-r := min_le_left _ _
        linarith
      have hlt := lt_trans hbr (EReal.coe_lt_coe_iff.mpr hgt)
      exact (not_lt_of_ge (hb (hm t ht ht1 true))) hlt
  refine ⟨hg, hu, ?_, ?_⟩
  · intro h
    have he := h.unique hg
    exact EReal.bot_ne_coe (0:ℝ) he
  · intro h
    have he := h.unique hu
    exact EReal.top_ne_coe (1:ℝ) he

/-- The complete T5 population witness. -/
theorem infinite_sharp_bounds_counterexample_proof :
    Assumptions boundedPassLaw ∧ boundedPassLaw alwaysPass = 1/3 ∧
    Atomless (boundedPassLaw.map observedY) ∧ FullRealSupport boundedPassLaw observedY ∧
    (∫ ω, observedY ω ∂boundedPassLaw) = 1/6 ∧
    (∫ ω, observedY ω ^ 2 ∂boundedPassLaw) = 13/63 ∧
    (∫ ω, |observedY ω| ^ 3 ∂boundedPassLaw) = 19/84 ∧
    Integrable (fun ω => |observedY ω| ^ 3) boundedPassLaw ∧
    (∀ R : ℝ, 1 ≤ R →
      (boundedPassLaw {ω | R < observedY ω}).toReal = 1/(3*(1+R)^5) ∧
      (boundedPassLaw {ω | observedY ω < -R}).toReal = 1/(3*(1+R)^5)) ∧
    (∀ a : Fin 2, passingRate boundedPassLaw a = 1/3 ∧ trimRatio boundedPassLaw a = 2 ∧
      (∀ m ∈ identifiedMeans boundedPassLaw a, 0 < m ∧ m < 1) ∧
      IsGLB (extendedMeans boundedPassLaw a) 0 ∧ IsLUB (extendedMeans boundedPassLaw a) 1 ∧
      ¬ IsGLB (extendedMeans boundedPassLaw a) ⊥ ∧ ¬ IsLUB (extendedMeans boundedPassLaw a) ⊤) ∧
    (∀ t : ℝ, 0 < t → t < 1 →
      (beta33 (Ioo 0 t)).toReal = 10*t^3 - 15*t^4 + 6*t^5 ∧
      (∀ upper : Bool, Compatible boundedPassLaw (betaEndpointLaw t upper)) ∧
      (∀ a : Fin 2,
        eventMean (betaEndpointLaw t false) (potentialY a) alwaysPass =
          t*(15/2-12*t+5*t^2)/(10-15*t+6*t^2) ∧
        0 < eventMean (betaEndpointLaw t false) (potentialY a) alwaysPass ∧
        eventMean (betaEndpointLaw t false) (potentialY a) alwaysPass < t ∧
        eventMean (betaEndpointLaw t true) (potentialY a) alwaysPass =
          1 - eventMean (betaEndpointLaw t false) (potentialY a) alwaysPass)) := by
  have ha := t5_joint_assumptions t5_bounded_joint
  refine ⟨ha.1, t5_bounded_always, t5_bounded_atomless, t5_bounded_fullsupport,
    t5_bounded_moments.1, t5_bounded_moments.2.1, t5_bounded_moments.2.2.1,
    t5_bounded_moments.2.2.2, t5_bounded_tails, ?_, ?_⟩
  · intro a
    exact ⟨(ha.2 a).1, (ha.2 a).2, t5_compatible_mean a, t5_extrema a⟩
  · intro t ht ht1
    exact ⟨t5_beta_cdf t ht.le ht1.le, t5_endpoint_tail_data t ht ht1⟩

end
end AronowAudit.P010.Wave1
