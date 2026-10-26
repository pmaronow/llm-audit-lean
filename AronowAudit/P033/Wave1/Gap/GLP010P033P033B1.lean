import AronowAudit.P010.Wave1.Gap.GP010P033B2
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-! P033-T12 and P033-T13: honest Gaussian intervals and their pseudo p-values. -/

namespace AronowAudit.P033.Wave1

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section

local instance instPseudoCounterNull (m : ℝ) : NullSingletonClass (gaussianReal m 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

lemma pseudo_counter_cdf_mono : StrictMono normalCDF := by
  intro x y hxy
  simpa only [normalCDF, cdf_eq_real] using P053.NormalCompletion.strictMono_normal_cdf hxy

lemma pseudo_counter_cdf_cont : Continuous normalCDF := by
  exact continuous_iff_continuousAt.mpr fun x =>
    (native_power_correction_cdf_deriv x).continuousAt

lemma pseudo_counter_cdf_zero : normalCDF 0 = 1/2 := by
  simpa only [normalCDF, cdf_eq_real] using P053.NormalCompletion.normal_cdf_zero

lemma pseudo_counter_quantile (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    normalCDF (normalQuantile p) = p := by
  obtain ⟨q, hq⟩ := P053.NormalCompletion.exists_cdf_eq (gaussianReal 0 1) hp hp1
  have hq' : normalCDF q = p := by simpa only [normalCDF, cdf_eq_real] using hq
  have hs : {x : ℝ | p ≤ normalCDF x} = Ici q := by
    ext x
    simp only [mem_setOf_eq, mem_Ici, ← hq']
    exact pseudo_counter_cdf_mono.le_iff_le
  rw [normalQuantile, hs, csInf_Ici, hq']

lemma pseudo_counter_coverage_even (b H : ℝ) : biasCoverage (-b) H = biasCoverage b H := by
  unfold biasCoverage
  rw [show -H - -b = -(H-b) by ring, native_power_correction_cdf_neg,
    show -H-b = -(H- -b) by ring, native_power_correction_cdf_neg]
  ring

lemma pseudo_counter_coverage_abs (b H : ℝ) : biasCoverage |b| H = biasCoverage b H := by
  rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg hb]
  · rw [abs_of_nonpos hb, pseudo_counter_coverage_even]

lemma pseudo_counter_coverage_zero (b : ℝ) : biasCoverage b 0 = 0 := by
  simp [biasCoverage]

lemma pseudo_counter_coverage_cont (b : ℝ) : Continuous (biasCoverage b) := by
  unfold biasCoverage
  exact (pseudo_counter_cdf_cont.comp (by fun_prop)).sub
    (pseudo_counter_cdf_cont.comp (by fun_prop))

lemma pseudo_counter_coverage_mono (b : ℝ) : StrictMono (biasCoverage b) := by
  intro H K hHK
  have h1 := pseudo_counter_cdf_mono (show H-b < K-b by linarith)
  have h2 := pseudo_counter_cdf_mono (show -K-b < -H-b by linarith)
  dsimp [biasCoverage]
  linarith

lemma pseudo_counter_coverage_limit (b : ℝ) :
    Tendsto (biasCoverage b) atTop (𝓝 1) := by
  have h1 : Tendsto (fun H : ℝ => normalCDF (H-b)) atTop (𝓝 1) :=
    by simpa only [Function.comp_def, id_eq, sub_eq_add_neg, normalCDF, cdf_eq_real] using
      (tendsto_cdf_atTop (gaussianReal 0 1)).comp
        (tendsto_atTop_add_const_right atTop (-b) tendsto_id)
  have h2 : Tendsto (fun H : ℝ => normalCDF (-H-b)) atTop (𝓝 0) :=
    by simpa only [Function.comp_def, sub_eq_add_neg, normalCDF, cdf_eq_real] using
      (tendsto_cdf_atBot (gaussianReal 0 1)).comp
        (tendsto_atBot_add_const_right atTop (-b) tendsto_neg_atTop_atBot)
  convert h1.sub h2 using 1
  · rfl
  · norm_num

lemma pseudo_counter_coverage_bias_deriv (H b : ℝ) :
    HasDerivAt (fun b => biasCoverage b H)
      (-normalDensity (H-b)+normalDensity (H+b)) b := by
  have h1 := (native_power_correction_cdf_deriv (H-b)).comp (x := b)
    ((hasDerivAt_id' b).const_sub H)
  have h2 := (native_power_correction_cdf_deriv (-H-b)).comp (x := b)
    ((hasDerivAt_id' b).const_sub (-H))
  have he : normalDensity (-H-b) = normalDensity (H+b) := by
    rw [show -H-b = -(H+b) by ring, native_power_correction_density_even]
  convert h1.sub h2 using 1
  · rfl
  · simp [he]

lemma pseudo_counter_coverage_bias_anti (H : ℝ) (hH : 0 < H) :
    StrictAntiOn (fun b => biasCoverage b H) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
    (continuous_iff_continuousAt.mpr (fun b =>
      (pseudo_counter_coverage_bias_deriv H b).continuousAt)).continuousOn
  intro b hb
  have hb0 : 0 < b := by simpa only [interior_Ici, mem_Ioi] using hb
  rw [(pseudo_counter_coverage_bias_deriv H b).deriv]
  have hd : normalDensity (H+b) < normalDensity (H-b) := by
    unfold normalDensity gaussianPDFReal
    norm_num only [NNReal.coe_one, mul_one, sub_zero]
    apply mul_lt_mul_of_pos_left
    · apply Real.exp_lt_exp.mpr
      nlinarith [mul_pos hH hb0]
    · positivity
  linarith

lemma pseudo_counter_root (B : ℝ) :
    (∃! H : ℝ, 0 < H ∧ biasCoverage B H = 19/20) ∧
    0 < honestHalfLength B ∧ biasCoverage B (honestHalfLength B) = 19/20 := by
  obtain ⟨K, hK⟩ := ((pseudo_counter_coverage_limit B).eventually
    (eventually_gt_nhds (by norm_num : (19/20 : ℝ) < 1))).exists
  have hK0 : 0 < K := by
    by_contra hn
    have hle := (pseudo_counter_coverage_mono B).monotone (le_of_not_gt hn)
    rw [pseudo_counter_coverage_zero] at hle
    linarith
  obtain ⟨H, hHmem, hH⟩ := intermediate_value_Icc hK0.le
    (pseudo_counter_coverage_cont B).continuousOn
    (show (19/20 : ℝ) ∈ Icc (biasCoverage B 0) (biasCoverage B K) by
      rw [pseudo_counter_coverage_zero]; exact ⟨by norm_num, hK.le⟩)
  have hH0 : 0 < H := by
    by_contra hn
    have hle := (pseudo_counter_coverage_mono B).monotone (le_of_not_gt hn)
    rw [pseudo_counter_coverage_zero, hH] at hle
    norm_num at hle
  have hs : {H : ℝ | 0 ≤ H ∧ 19/20 ≤ biasCoverage B H} = Ici H := by
    ext x
    simp only [mem_setOf_eq, mem_Ici, ← hH, (pseudo_counter_coverage_mono B).le_iff_le]
    exact ⟨fun hx => hx.2, fun hx => ⟨hH0.le.trans hx, hx⟩⟩
  have he : honestHalfLength B = H := by rw [honestHalfLength, hs, csInf_Ici]
  refine ⟨⟨H, ⟨hH0, hH⟩, ?_⟩, ?_⟩
  · intro x hx
    exact (pseudo_counter_coverage_mono B).injective (hx.2.trans hH.symm)
  · simpa only [he] using And.intro hH0 hH

lemma pseudo_counter_worst_coverage (B b H : ℝ) (hB : 0 ≤ B)
    (hb : |b| ≤ B) (hH : 0 < H) :
    biasCoverage B H ≤ biasCoverage b H ∧
      (biasCoverage b H = biasCoverage B H ↔ |b| = B) := by
  rw [← pseudo_counter_coverage_abs b H]
  have ha := pseudo_counter_coverage_bias_anti H hH
  refine ⟨ha.antitoneOn (abs_nonneg b) hB hb, ?_⟩
  exact ⟨fun h => ha.injOn (abs_nonneg b) hB h,
    fun h => congrArg (fun x => biasCoverage x H) h⟩

lemma pseudo_counter_interval_mass (m l u : ℝ) (hlu : l ≤ u) :
    (gaussianReal m 1).real (Icc l u) = normalCDF (u-m)-normalCDF (l-m) := by
  have hcont := (P053.NormalCompletion.cdf_continuousAt (gaussianReal m 1) l).continuousWithinAt
    (s := Iic l)
  have he : gaussianReal m 1 (Icc l u) =
      ENNReal.ofReal (cdf (gaussianReal m 1) u - cdf (gaussianReal m 1) l) := by
    conv_lhs => rw [← measure_cdf (gaussianReal m 1), StieltjesFunction.measure_Icc,
      hcont.leftLim_eq]
  rw [measureReal_def, he, ENNReal.toReal_ofReal
    (sub_nonneg.mpr (monotone_cdf _ hlu)), cdf_eq_real, cdf_eq_real,
    native_power_correction_shifted_cdf, native_power_correction_shifted_cdf]

lemma pseudo_counter_actual_coverage (θ b H : ℝ) (hH : 0 ≤ H) :
    intervalCoverage (biasModelLaw θ b) id θ H = biasCoverage b H := by
  have hs : {t : ℝ | θ ∈ Icc (id t-H) (id t+H)} = Icc (θ-H) (θ+H) := by
    ext t
    simp only [mem_setOf_eq, mem_Icc, id_eq]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rw [intervalCoverage, hs, biasModelLaw, pseudo_counter_interval_mass _ _ _ (by linarith)]
  simp only [biasCoverage, show θ+H-(θ+b) = H-b by ring,
    show θ-H-(θ+b) = -H-b by ring]

lemma pseudo_counter_tail_strict (b c : ℝ) (hc : 0 ≤ c) :
    (biasModelLaw 0 b).real {t | c < |t|} = 1-biasCoverage b c := by
  have hs : {t : ℝ | c < |t|} = (Icc (-c) c)ᶜ := by
    ext t
    simp only [mem_setOf_eq, mem_compl_iff, mem_Icc, ← abs_le, not_le]
  rw [hs, biasModelLaw, zero_add, measureReal_compl measurableSet_Icc, probReal_univ,
    pseudo_counter_interval_mass _ _ _ (by linarith)]
  rfl

lemma pseudo_counter_tail_weak (b c : ℝ) (hc : 0 < c) :
    (biasModelLaw 0 b).real {t | c ≤ |t|} = 1-biasCoverage b c := by
  have hs : {t : ℝ | c ≤ |t|} = Iic (-c) ∪ Ici c := by
    ext t
    simp only [mem_setOf_eq, mem_union, mem_Iic, mem_Ici, le_abs]
    constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)
  have ht : {t : ℝ | c < |t|} = Iio (-c) ∪ Ioi c := by
    ext t
    simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi, lt_abs]
    constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)
  rw [← pseudo_counter_tail_strict b c hc.le, hs, ht]
  simp only [biasModelLaw, zero_add]
  apply measureReal_congr
  exact (Iio_ae_eq_Iic' (measure_singleton (-c))).symm.union
    (Ioi_ae_eq_Ici' (measure_singleton c)).symm

lemma pseudo_counter_tail_formula (b c : ℝ) :
    1-biasCoverage b c = normalCDF (b-c)+normalCDF (-b-c) := by
  rw [biasCoverage, show b-c = -(c-b) by ring, native_power_correction_cdf_neg]
  rw [show -c-b = -b-c by ring]
  ring

/-! The next Taylor and integral lemmas adapt this repository's exponential-polynomial
bounds for P041, P042, and P045. -/

def pseudo_counter_expPoly (n : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (-u)^j / (j.factorial:ℝ)

def pseudo_counter_intPoly (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (-1/2:ℝ)^j * x^(2*j+1) / ((j.factorial:ℝ)*(2*j+1))

lemma pseudo_counter_iter_exp (n : ℕ) : iteratedDeriv n Real.exp = Real.exp := by
  simpa using iteratedDeriv_exp_const_mul n 1

lemma pseudo_counter_exp_taylor (n : ℕ) (u : ℝ) (hu : u ≠ 0) :
    taylorWithinEval Real.exp n (uIcc 0 (-u)) 0 (-u) = pseudo_counter_expPoly n u := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by simpa using hu))
    (Real.contDiff_exp (n := j)).contDiffAt (left_mem_uIcc), pseudo_counter_iter_exp]
  simp [Real.exp_zero, div_eq_mul_inv, mul_comm]

lemma pseudo_counter_exp_bracket (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    pseudo_counter_expPoly (2*n+1) u ≤ Real.exp (-u) ∧ Real.exp (-u) ≤ pseudo_counter_expPoly (2*n) u := by
  by_cases hzero : u = 0
  · subst u
    have hz (k : ℕ) : pseudo_counter_expPoly k 0 = 1 := by
      unfold pseudo_counter_expPoly
      calc
        _ = (-(0:ℝ))^0 / (Nat.factorial 0:ℝ) :=
          Finset.sum_eq_single 0 (by intro b hb hb0; simp [hb0]) (by simp)
        _ = 1 := by norm_num
    simp [hz]
  have hx : (0:ℝ) ≠ -u := by intro h; apply hzero; linarith
  have rem (k : ℕ) := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.exp) (n := k) hx Real.contDiff_exp.contDiffOn
  obtain ⟨a,ha,he⟩ := rem (2*n+1)
  obtain ⟨b,hb,hf⟩ := rem (2*n)
  rw [pseudo_counter_exp_taylor _ _ hzero, pseudo_counter_iter_exp] at he hf
  simp only [sub_zero] at he hf
  constructor
  · have hp : 0 ≤ Real.exp a * (-u)^(2*n+1+1) / ((2*n+1+1).factorial:ℝ) := by
      apply div_nonneg
      · apply mul_nonneg (Real.exp_pos _).le
        convert sq_nonneg ((-u)^(n+1)) using 1 <;> ring
      · positivity
    linarith
  · have hp : Real.exp b * (-u)^(2*n+1) / ((2*n+1).factorial:ℝ) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        rw [pow_succ, pow_mul]
        exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (sq_nonneg _) _) (neg_nonpos.mpr hu)
      · positivity
    linarith

lemma pseudo_counter_poly_integral (n : ℕ) (x : ℝ) :
    (∫ t in 0..x, pseudo_counter_expPoly n (t^2/2)) = pseudo_counter_intPoly n x := by
  have he (t : ℝ) (j : ℕ) : (-(t^2/2))^j / (j.factorial:ℝ) =
      ((-1/2:ℝ)^j / (j.factorial:ℝ)) * t^(2*j) := by
    rw [show -(t^2/2) = (-1/2:ℝ)*t^2 by ring, mul_pow, ← pow_mul]
    ring
  simp only [pseudo_counter_expPoly, he]
  rw [intervalIntegral.integral_finsetSum (fun j _ => (by fun_prop :
    Continuous (fun t : ℝ => ((-1/2:ℝ)^j / (j.factorial:ℝ)) * t^(2*j))).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, integral_pow, zero_pow (by omega : 2*_+1 ≠ 0), sub_zero]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma pseudo_counter_integral_bracket (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    pseudo_counter_intPoly (2*n+1) x ≤ (∫ t in 0..x, Real.exp (-(t^2/2))) ∧
    (∫ t in 0..x, Real.exp (-(t^2/2))) ≤ pseudo_counter_intPoly (2*n) x := by
  have hp (k : ℕ) : Continuous (fun t : ℝ => pseudo_counter_expPoly k (t^2/2)) := by
    unfold pseudo_counter_expPoly
    fun_prop
  have hf : Continuous (fun t : ℝ => Real.exp (-(t^2/2))) := by fun_prop
  rw [← pseudo_counter_poly_integral, ← pseudo_counter_poly_integral]
  constructor
  · exact intervalIntegral.integral_mono_on hx ((hp _).intervalIntegrable _ _)
      (hf.intervalIntegrable _ _) (fun t _ => (pseudo_counter_exp_bracket n (t^2/2) (by positivity)).1)
  · exact intervalIntegral.integral_mono_on hx (hf.intervalIntegrable _ _)
      ((hp _).intervalIntegrable _ _) (fun t _ => (pseudo_counter_exp_bracket n (t^2/2) (by positivity)).2)

lemma pseudo_counter_cdf_integral_formula (x : ℝ) (hx : 0 ≤ x) :
    2*cdf (gaussianReal 0 1) (-x) =
      1 - 2*(1/Real.sqrt (2*Real.pi))*(∫ t in 0..x, Real.exp (-(t^2/2))) := by
  have hm : gaussianReal 0 1 (Ioc 0 x) =
      ENNReal.ofReal (cdf (gaussianReal 0 1) x - cdf (gaussianReal 0 1) 0) := by
    conv_lhs => rw [← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc]
  rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1:NNReal) ≠ 0)] at hm
  have hn : 0 ≤ cdf (gaussianReal 0 1) x - cdf (gaussianReal 0 1) 0 :=
    sub_nonneg.mpr (monotone_cdf _ hx)
  have hint : 0 ≤ ∫ t in Ioc 0 x, gaussianPDFReal 0 1 t :=
    integral_nonneg (fun t => gaussianPDFReal_nonneg 0 1 t)
  have he := (ENNReal.ofReal_eq_ofReal_iff hint hn).mp hm
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero] at he
  rw [← intervalIntegral.integral_of_le hx, intervalIntegral.integral_const_mul] at he
  simp only [neg_div] at he
  rw [P053.NormalCompletion.normal_cdf_zero] at he
  rw [P053.NormalCompletion.normal_cdf_neg]
  simp only [one_div]
  nlinarith only [he]


lemma pseudo_counter_normalizer :
    (0.39894228040143267793 : ℝ) ≤ 1/Real.sqrt (2*Real.pi) ∧
    1/Real.sqrt (2*Real.pi) ≤ 0.39894228040143267795 := by
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  constructor
  · apply (le_div_iff₀ hs).mpr
    nlinarith [Real.pi_lt_d20,
      sq_nonneg (0.39894228040143267793*Real.sqrt (2*Real.pi)-1)]
  · apply (div_le_iff₀ hs).mpr
    nlinarith [Real.pi_gt_d20,
      sq_nonneg (0.39894228040143267795*Real.sqrt (2*Real.pi)-1)]

lemma pseudo_counter_cdf_bracket (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hp : 0 ≤ pseudo_counter_intPoly (2*n+1) x) :
    1/2 + 0.39894228040143267793*pseudo_counter_intPoly (2*n+1) x ≤ normalCDF x ∧
    normalCDF x ≤ 1/2 + 0.39894228040143267795*pseudo_counter_intPoly (2*n) x := by
  obtain ⟨hl,hu⟩ := pseudo_counter_integral_bracket n x hx
  obtain ⟨hc0,hc1⟩ := pseudo_counter_normalizer
  have hi : 0 ≤ ∫ t in 0..x, Real.exp (-(t^2/2)) :=
    intervalIntegral.integral_nonneg hx (fun t _ => (Real.exp_pos _).le)
  have hcoef : 0 ≤ 1/Real.sqrt (2*Real.pi) := by positivity
  have he := pseudo_counter_cdf_integral_formula x hx
  rw [P053.NormalCompletion.normal_cdf_neg] at he
  rw [cdf_eq_real] at he
  simp only [normalCDF]
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hl hcoef
    have h2 := mul_le_mul_of_nonneg_right hc0 hp
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hu hcoef
    have h2 := mul_le_mul_of_nonneg_right hc1 (le_trans hi hu)
    nlinarith

lemma pseudo_counter_cdf_certificate (n : ℕ) (x L U : ℝ) (hx : 0 ≤ x)
    (hL0 : 1/2 ≤ L)
    (hL : L ≤ 1/2 + 0.39894228040143267793*pseudo_counter_intPoly (2*n+1) x)
    (hU : 1/2 + 0.39894228040143267795*pseudo_counter_intPoly (2*n) x ≤ U) :
    L ≤ normalCDF x ∧ normalCDF x ≤ U := by
  have hp : 0 ≤ pseudo_counter_intPoly (2*n+1) x := by nlinarith only [hL0, hL]
  obtain ⟨hl,hu⟩ := pseudo_counter_cdf_bracket n x hx hp
  exact ⟨hL.trans hl, hu.trans hU⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_0 :
    (97499999999999999791/10^20 : ℝ) ≤ normalCDF 1.9599639845400542 ∧
    normalCDF 1.9599639845400542 ≤ 97499999999999999794/10^20 := by
  apply pseudo_counter_cdf_certificate 16 1.9599639845400542 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_1 :
    (97500000000000000375/10^20 : ℝ) ≤ normalCDF 1.9599639845400543 ∧
    normalCDF 1.9599639845400543 ≤ 97500000000000000379/10^20 := by
  apply pseudo_counter_cdf_certificate 16 1.9599639845400543 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_2 :
    (89999999999999998823/10^20 : ℝ) ≤ normalCDF 1.2815515655446004 ∧
    normalCDF 1.2815515655446004 ≤ 89999999999999998826/10^20 := by
  apply pseudo_counter_cdf_certificate 16 1.2815515655446004 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_3 :
    (90000000000000000578/10^20 : ℝ) ≤ normalCDF 1.2815515655446005 ∧
    normalCDF 1.2815515655446005 ≤ 90000000000000000581/10^20 := by
  apply pseudo_counter_cdf_certificate 16 1.2815515655446005 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_4 :
    (95013310161783609040/10^20 : ℝ) ≤ normalCDF 1.6461455482153111 ∧
    normalCDF 1.6461455482153111 ≤ 95013310161783609043/10^20 := by
  apply pseudo_counter_cdf_certificate 16 1.6461455482153111 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_5 :
    (99986689838216390569/10^20 : ℝ) ≤ normalCDF 3.6461455482153111 ∧
    normalCDF 3.6461455482153111 ≤ 99986689838216390573/10^20 := by
  apply pseudo_counter_cdf_certificate 24 3.6461455482153111 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_6 :
    (95013310161783610069/10^20 : ℝ) ≤ normalCDF 1.6461455482153112 ∧
    normalCDF 1.6461455482153112 ≤ 95013310161783610073/10^20 := by
  apply pseudo_counter_cdf_certificate 16 1.6461455482153112 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_7 :
    (99986689838216390574/10^20 : ℝ) ≤ normalCDF 3.6461455482153112 ∧
    normalCDF 3.6461455482153112 ≤ 99986689838216390578/10^20 := by
  apply pseudo_counter_cdf_certificate 24 3.6461455482153112 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_8 :
    (95366489279903952223/10^20 : ℝ) ≤ normalCDF 1.6814774423281543 ∧
    normalCDF 1.6814774423281543 ≤ 95366489279903952226/10^20 := by
  apply pseudo_counter_cdf_certificate 16 1.6814774423281543 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_9 :
    (99633510720096046791/10^20 : ℝ) ≤ normalCDF 2.6814774423281543 ∧
    normalCDF 2.6814774423281543 ≤ 99633510720096046795/10^20 := by
  apply pseudo_counter_cdf_certificate 24 2.6814774423281543 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_10 :
    (95366489279903953193/10^20 : ℝ) ≤ normalCDF 1.6814774423281544 ∧
    normalCDF 1.6814774423281544 ≤ 95366489279903953197/10^20 := by
  apply pseudo_counter_cdf_certificate 16 1.6814774423281544 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_11 :
    (99633510720096046901/10^20 : ℝ) ≤ normalCDF 2.6814774423281544 ∧
    normalCDF 2.6814774423281544 ≤ 99633510720096046904/10^20 := by
  apply pseudo_counter_cdf_certificate 24 2.6814774423281544 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

lemma pseudo_counter_coverage_symmetric (b H : ℝ) :
    biasCoverage b H = normalCDF (H-b)+normalCDF (H+b)-1 := by
  unfold biasCoverage
  rw [show -H-b = -(H+b) by ring, native_power_correction_cdf_neg]
  ring

lemma pseudo_counter_quantile_bounds :
    (1.9599639845400542 : ℝ) < normalCritical ∧ normalCritical < 1.9599639845400543 ∧
    (1.2815515655446004 : ℝ) < normalQuantile (9/10) ∧
      normalQuantile (9/10) < 1.2815515655446005 := by
  have hz := native_power_correction_critical_cdf
  have hq := pseudo_counter_quantile (9/10) (by norm_num) (by norm_num)
  refine ⟨pseudo_counter_cdf_mono.lt_iff_lt.mp ?_,
    pseudo_counter_cdf_mono.lt_iff_lt.mp ?_,
    pseudo_counter_cdf_mono.lt_iff_lt.mp ?_,
    pseudo_counter_cdf_mono.lt_iff_lt.mp ?_⟩
  · linarith only [hz, pseudo_counter_cdf_num_0.2]
  · linarith only [hz, pseudo_counter_cdf_num_1.1]
  · linarith only [hq, pseudo_counter_cdf_num_2.2]
  · linarith only [hq, pseudo_counter_cdf_num_3.1]

lemma pseudo_counter_honest_bounds :
    (2.6461455482153111 : ℝ) < honestHalfLength 1 ∧
    honestHalfLength 1 < 2.6461455482153112 ∧
    (2.1814774423281543 : ℝ) < honestHalfLength (1/2) ∧
    honestHalfLength (1/2) < 2.1814774423281544 := by
  have h1 := (pseudo_counter_root 1).2.2
  have h2 := (pseudo_counter_root (1/2)).2.2
  refine ⟨(pseudo_counter_coverage_mono 1).lt_iff_lt.mp ?_,
    (pseudo_counter_coverage_mono 1).lt_iff_lt.mp ?_,
    (pseudo_counter_coverage_mono (1/2)).lt_iff_lt.mp ?_,
    (pseudo_counter_coverage_mono (1/2)).lt_iff_lt.mp ?_⟩
  · rw [h1, pseudo_counter_coverage_symmetric]
    norm_num only
    linarith only [h1, pseudo_counter_cdf_num_4.2, pseudo_counter_cdf_num_5.2]
  · rw [h1, pseudo_counter_coverage_symmetric]
    norm_num only
    linarith only [h1, pseudo_counter_cdf_num_6.1, pseudo_counter_cdf_num_7.1]
  · rw [h2, pseudo_counter_coverage_symmetric]
    norm_num only
    linarith only [h2, pseudo_counter_cdf_num_8.2, pseudo_counter_cdf_num_9.2]
  · rw [h2, pseudo_counter_coverage_symmetric]
    norm_num only
    linarith only [h2, pseudo_counter_cdf_num_10.1, pseudo_counter_cdf_num_11.1]

lemma pseudo_counter_quantile_pos (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < normalQuantile (1-α/2) := by
  apply pseudo_counter_cdf_mono.lt_iff_lt.mp
  rw [pseudo_counter_cdf_zero,
    pseudo_counter_quantile _ (by linarith) (by linarith)]
  linarith

lemma pseudo_counter_pseudo_iff (t h α : ℝ) (hh : 0 < h)
    (hα : 0 < α) (hα1 : α < 1) :
    pseudoP t h ≤ α ↔ h*normalQuantile (1-α/2)/normalCritical ≤ |t| := by
  have hz := native_power_correction_critical_pos
  have hq := pseudo_counter_quantile (1-α/2) (by linarith) (by linarith)
  have hneg : normalCDF (-normalQuantile (1-α/2)) = α/2 := by
    rw [native_power_correction_cdf_neg, hq]; ring
  calc
    pseudoP t h ≤ α ↔ normalCDF (-normalCritical*|t|/h) ≤
        normalCDF (-normalQuantile (1-α/2)) := by
      rw [hneg]
      unfold pseudoP
      constructor <;> intro ht <;> linarith
    _ ↔ -normalCritical*|t|/h ≤ -normalQuantile (1-α/2) :=
      pseudo_counter_cdf_mono.le_iff_le
    _ ↔ h*normalQuantile (1-α/2)/normalCritical ≤ |t| := by
      rw [div_le_iff₀ hh, div_le_iff₀ hz]
      constructor <;> intro ht <;> nlinarith only [ht]

lemma pseudo_counter_pseudo_tail (B h α : ℝ) (hh : 0 < h)
    (hα : 0 < α) (hα1 : α < 1) :
    (biasModelLaw 0 B).real {t | pseudoP t h ≤ α} =
      normalCDF (B-h*normalQuantile (1-α/2)/normalCritical)+
      normalCDF (-B-h*normalQuantile (1-α/2)/normalCritical) := by
  have hc : 0 < h*normalQuantile (1-α/2)/normalCritical :=
    div_pos (mul_pos hh (pseudo_counter_quantile_pos α hα hα1))
      native_power_correction_critical_pos
  have hs : {t | pseudoP t h ≤ α} =
      {t | h*normalQuantile (1-α/2)/normalCritical ≤ |t|} := by
    ext t
    exact pseudo_counter_pseudo_iff t h α hh hα hα1
  rw [hs, pseudo_counter_tail_weak B _ hc, pseudo_counter_tail_formula]

lemma pseudo_counter_cutoff_bounds :
    (1.7302215738265286 : ℝ) < honestHalfLength 1*normalQuantile (9/10)/normalCritical ∧
    honestHalfLength 1*normalQuantile (9/10)/normalCritical < 1.7302215738265291 ∧
    (1.4263914303874004 : ℝ) < honestHalfLength (1/2)*normalQuantile (9/10)/normalCritical ∧
    honestHalfLength (1/2)*normalQuantile (9/10)/normalCritical < 1.4263914303874008 := by
  obtain ⟨hzl,hzu,hql,hqu⟩ := pseudo_counter_quantile_bounds
  obtain ⟨h1l,h1u,h2l,h2u⟩ := pseudo_counter_honest_bounds
  have hz := native_power_correction_critical_pos
  have hq : 0 < normalQuantile (9/10) := by linarith
  have h1lo := (mul_lt_mul_of_pos_left hql
    (by norm_num : (0:ℝ) < 2.6461455482153111)).trans (mul_lt_mul_of_pos_right h1l hq)
  have h1hi := (mul_lt_mul_of_pos_right h1u hq).trans
    (mul_lt_mul_of_pos_left hqu (by norm_num : (0:ℝ) < 2.6461455482153112))
  have h2lo := (mul_lt_mul_of_pos_left hql
    (by norm_num : (0:ℝ) < 2.1814774423281543)).trans (mul_lt_mul_of_pos_right h2l hq)
  have h2hi := (mul_lt_mul_of_pos_right h2u hq).trans
    (mul_lt_mul_of_pos_left hqu (by norm_num : (0:ℝ) < 2.1814774423281544))
  refine ⟨(lt_div_iff₀ hz).mpr ?_, (div_lt_iff₀ hz).mpr ?_,
    (lt_div_iff₀ hz).mpr ?_, (div_lt_iff₀ hz).mpr ?_⟩ <;> nlinarith
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_12 :
    (76737262125683675441/10^20 : ℝ) ≤ normalCDF 0.7302215738265286 ∧
    normalCDF 0.7302215738265286 ≤ 76737262125683675444/10^20 := by
  apply pseudo_counter_cdf_certificate 16 0.7302215738265286 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_13 :
    (99683541147217149610/10^20 : ℝ) ≤ normalCDF 2.7302215738265286 ∧
    normalCDF 2.7302215738265286 ≤ 99683541147217149613/10^20 := by
  apply pseudo_counter_cdf_certificate 24 2.7302215738265286 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_14 :
    (76737262125683690720/10^20 : ℝ) ≤ normalCDF 0.7302215738265291 ∧
    normalCDF 0.7302215738265291 ≤ 76737262125683690723/10^20 := by
  apply pseudo_counter_cdf_certificate 16 0.7302215738265291 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_15 :
    (99683541147217150090/10^20 : ℝ) ≤ normalCDF 2.7302215738265291 ∧
    normalCDF 2.7302215738265291 ≤ 99683541147217150093/10^20 := by
  apply pseudo_counter_cdf_certificate 24 2.7302215738265291 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_16 :
    (82287870200393386612/10^20 : ℝ) ≤ normalCDF 0.9263914303874004 ∧
    normalCDF 0.9263914303874004 ≤ 82287870200393386615/10^20 := by
  apply pseudo_counter_cdf_certificate 16 0.9263914303874004 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_17 :
    (97297224166835432272/10^20 : ℝ) ≤ normalCDF 1.9263914303874004 ∧
    normalCDF 1.9263914303874004 ≤ 97297224166835432275/10^20 := by
  apply pseudo_counter_cdf_certificate 16 1.9263914303874004 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_18 :
    (82287870200393397002/10^20 : ℝ) ≤ normalCDF 0.9263914303874008 ∧
    normalCDF 0.9263914303874008 ≤ 82287870200393397005/10^20 := by
  apply pseudo_counter_cdf_certificate 16 0.9263914303874008 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma pseudo_counter_cdf_num_19 :
    (97297224166835434767/10^20 : ℝ) ≤ normalCDF 1.9263914303874008 ∧
    normalCDF 1.9263914303874008 ≤ 97297224166835434770/10^20 := by
  apply pseudo_counter_cdf_certificate 16 1.9263914303874008 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

lemma pseudo_counter_rejection_bounds :
    ((23579196727091/10^14 : ℝ) <
      (biasModelLaw 0 1).real {t | pseudoP t (honestHalfLength 1) ≤ 1/5} ∧
      (biasModelLaw 0 1).real {t | pseudoP t (honestHalfLength 1) ≤ 1/5} < 23579196727101/10^14) ∧
    ((20414905632765/10^14 : ℝ) <
      (biasModelLaw 0 (1/2)).real {t | pseudoP t (honestHalfLength (1/2)) ≤ 1/5} ∧
      (biasModelLaw 0 (1/2)).real {t | pseudoP t (honestHalfLength (1/2)) ≤ 1/5} < 20414905632774/10^14) := by
  have he1 := pseudo_counter_pseudo_tail 1 (honestHalfLength 1) (1/5)
    (pseudo_counter_root 1).2.1 (by norm_num) (by norm_num)
  have he2 := pseudo_counter_pseudo_tail (1/2) (honestHalfLength (1/2)) (1/5)
    (pseudo_counter_root (1/2)).2.1 (by norm_num) (by norm_num)
  rw [← pseudo_counter_tail_formula] at he1 he2
  norm_num only at he1 he2
  rw [he1, he2]
  obtain ⟨h1l,h1u,h2l,h2u⟩ := pseudo_counter_cutoff_bounds
  have h1lo := (pseudo_counter_coverage_mono 1).monotone h1l.le
  have h1hi := (pseudo_counter_coverage_mono 1).monotone h1u.le
  have h2lo := (pseudo_counter_coverage_mono (1/2)).monotone h2l.le
  have h2hi := (pseudo_counter_coverage_mono (1/2)).monotone h2u.le
  rw [pseudo_counter_coverage_symmetric 1 (1.7302215738265286)] at h1lo
  rw [pseudo_counter_coverage_symmetric 1 (1.7302215738265291)] at h1hi
  rw [pseudo_counter_coverage_symmetric (1/2) (1.4263914303874004)] at h2lo
  rw [pseudo_counter_coverage_symmetric (1/2) (1.4263914303874008)] at h2hi
  norm_num only at h1lo h1hi h2lo h2hi
  constructor
  · constructor
    · linarith only [h1hi, pseudo_counter_cdf_num_14.2, pseudo_counter_cdf_num_15.2]
    · linarith only [h1lo, pseudo_counter_cdf_num_12.1, pseudo_counter_cdf_num_13.1]
  · constructor
    · linarith only [h2hi, pseudo_counter_cdf_num_18.2, pseudo_counter_cdf_num_19.2]
    · linarith only [h2lo, pseudo_counter_cdf_num_16.1, pseudo_counter_cdf_num_17.1]

theorem pseudo_p_counterexample_proof :
    (∃! H : ℝ, 0 < H ∧ biasCoverage 1 H = 19/20) ∧
    0 < honestHalfLength 1 ∧ biasCoverage 1 (honestHalfLength 1) = 19/20 ∧
    ((264614554821530/10^14:ℝ) < honestHalfLength 1 ∧
      honestHalfLength 1 < 264614554821540/10^14) ∧
    (∀ θ b : ℝ, |b| ≤ 1 →
      intervalCoverage (biasModelLaw θ b) id θ (honestHalfLength 1) =
        biasCoverage b (honestHalfLength 1) ∧
      19/20 ≤ intervalCoverage (biasModelLaw θ b) id θ (honestHalfLength 1) ∧
      (intervalCoverage (biasModelLaw θ b) id θ (honestHalfLength 1) = 19/20 ↔ |b| = 1)) ∧
    ((195996398454000/10^14:ℝ) < normalCritical ∧ normalCritical < 195996398454010/10^14) ∧
    ((128155156554460/10^14:ℝ) < normalQuantile (9/10) ∧
      normalQuantile (9/10) < 128155156554470/10^14) ∧
    (let C := honestHalfLength 1 * normalQuantile (9/10)/normalCritical;
      (173022157382648/10^14:ℝ) < C ∧ C < 173022157382677/10^14 ∧
      {t | pseudoP t (honestHalfLength 1) ≤ 1/5} = {t | C ≤ |t|} ∧
      (biasModelLaw 0 1).real {t | pseudoP t (honestHalfLength 1) ≤ 1/5} =
        normalCDF (1-C)+normalCDF (-1-C)) ∧
    ((23579196727091/10^14:ℝ) <
      (biasModelLaw 0 1).real {t | pseudoP t (honestHalfLength 1) ≤ 1/5} ∧
      (biasModelLaw 0 1).real {t | pseudoP t (honestHalfLength 1) ≤ 1/5} < 23579196727101/10^14) ∧
    (∃! H : ℝ, 0 < H ∧ biasCoverage (1/2) H = 19/20) ∧
    0 < honestHalfLength (1/2) ∧ biasCoverage (1/2) (honestHalfLength (1/2)) = 19/20 ∧
    ((218147744232810/10^14:ℝ) < honestHalfLength (1/2) ∧
      honestHalfLength (1/2) < 218147744232820/10^14) ∧
    ((20414905632765/10^14:ℝ) <
      (biasModelLaw 0 (1/2)).real {t | pseudoP t (honestHalfLength (1/2)) ≤ 1/5} ∧
      (biasModelLaw 0 (1/2)).real {t | pseudoP t (honestHalfLength (1/2)) ≤ 1/5} < 20414905632774/10^14) ∧
    ¬ ValidBiasP 1 (fun t => pseudoP t (honestHalfLength 1)) ∧
    ¬ ValidBiasP (1/2) (fun t => pseudoP t (honestHalfLength (1/2))) := by
  have hr1 := pseudo_counter_root 1
  have hr2 := pseudo_counter_root (1/2)
  obtain ⟨h1l,h1u,h2l,h2u⟩ := pseudo_counter_honest_bounds
  obtain ⟨hzl,hzu,hql,hqu⟩ := pseudo_counter_quantile_bounds
  have hp := pseudo_counter_rejection_bounds
  refine ⟨hr1.1, hr1.2.1, hr1.2.2, ?_, ?_, ?_, ?_, ?_, hp.1,
    hr2.1, hr2.2.1, hr2.2.2, ?_, hp.2, ?_, ?_⟩
  · constructor <;> linarith
  · intro θ b hb
    have hc := pseudo_counter_actual_coverage θ b (honestHalfLength 1) hr1.2.1.le
    have hw := pseudo_counter_worst_coverage 1 b (honestHalfLength 1)
      (by norm_num) hb hr1.2.1
    rw [hr1.2.2] at hw
    exact ⟨hc, hc.symm ▸ hw.1, by rw [hc]; exact hw.2⟩
  · constructor <;> linarith
  · constructor <;> linarith
  · dsimp only
    obtain ⟨hCl,hCu,_,_⟩ := pseudo_counter_cutoff_bounds
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · ext t
      simpa only [mem_setOf_eq, show (1-(1/5:ℝ)/2) = 9/10 by norm_num] using
        pseudo_counter_pseudo_iff t (honestHalfLength 1) (1/5) hr1.2.1
          (by norm_num) (by norm_num)
    · simpa only [show (1-(1/5:ℝ)/2) = 9/10 by norm_num] using
        pseudo_counter_pseudo_tail 1 (honestHalfLength 1) (1/5) hr1.2.1
          (by norm_num) (by norm_num)
  · constructor <;> linarith
  · intro hv
    have h := hv 1 (by norm_num) (1/5) (by norm_num) (by norm_num)
    linarith only [h, hp.1.1]
  · intro hv
    have h := hv (1/2) (by norm_num) (1/5) (by norm_num) (by norm_num)
    linarith only [h, hp.2.1]

lemma pseudo_correct_geometry (t h : ℝ) (hh : 0 < h) :
    ((|t|/(h/normalCritical)) = normalCritical*|t|/h) ∧
    (pseudoP t h < 1/20 ↔ h < |t|) ∧
    (pseudoP t h < 1/20 ↔ 0 ∉ Icc (t-h) (t+h)) ∧
    (pseudoP t h ≤ 1/20 ↔ h ≤ |t|) := by
  have hz := native_power_correction_critical_pos
  have hn : normalCDF (-normalCritical) = 1/40 := by
    rw [native_power_correction_cdf_neg, native_power_correction_critical_cdf]
    norm_num
  have hlt : pseudoP t h < 1/20 ↔ h < |t| := by
    calc
      pseudoP t h < 1/20 ↔ normalCDF (-normalCritical*|t|/h) <
          normalCDF (-normalCritical) := by
        rw [hn]
        unfold pseudoP
        constructor <;> intro ht <;> linarith
      _ ↔ -normalCritical*|t|/h < -normalCritical := pseudo_counter_cdf_mono.lt_iff_lt
      _ ↔ h < |t| := by
        rw [div_lt_iff₀ hh]
        constructor <;> intro ht <;> nlinarith [mul_pos hz (sub_pos.mpr ht)]
  have hle : pseudoP t h ≤ 1/20 ↔ h ≤ |t| := by
    calc
      pseudoP t h ≤ 1/20 ↔ normalCDF (-normalCritical*|t|/h) ≤
          normalCDF (-normalCritical) := by
        rw [hn]
        unfold pseudoP
        constructor <;> intro ht <;> linarith
      _ ↔ -normalCritical*|t|/h ≤ -normalCritical := pseudo_counter_cdf_mono.le_iff_le
      _ ↔ h ≤ |t| := by
        rw [div_le_iff₀ hh]
        constructor <;> intro ht <;> nlinarith
  refine ⟨?_, hlt, ?_, hle⟩
  · field_simp
  · rw [zero_in_interval, not_le]
    exact hlt

lemma pseudo_correct_honest_size (B : ℝ) (hB : 0 ≤ B) :
    (∃! H : ℝ, 0 < H ∧ biasCoverage B H = 19/20) ∧
    0 < honestHalfLength B ∧ biasCoverage B (honestHalfLength B) = 19/20 ∧
    (∀ b : ℝ, |b| ≤ B →
      (biasModelLaw 0 b).real {t | pseudoP t (honestHalfLength B) < 1/20} =
        1-biasCoverage b (honestHalfLength B) ∧
      (biasModelLaw 0 b).real {t | pseudoP t (honestHalfLength B) < 1/20} ≤ 1/20 ∧
      ((biasModelLaw 0 b).real {t | pseudoP t (honestHalfLength B) < 1/20} = 1/20 ↔ |b| = B)) := by
  have hr := pseudo_counter_root B
  refine ⟨hr.1, hr.2.1, hr.2.2, ?_⟩
  intro b hb
  have hs : {t | pseudoP t (honestHalfLength B) < 1/20} =
      {t | honestHalfLength B < |t|} := by
    ext t
    exact (pseudo_correct_geometry t _ hr.2.1).2.1
  rw [hs, pseudo_counter_tail_strict b _ hr.2.1.le]
  have hw := pseudo_counter_worst_coverage B b _ hB hb hr.2.1
  rw [hr.2.2] at hw
  refine ⟨rfl, by linarith only [hw.1], ?_⟩
  rw [← hw.2]
  constructor <;> intro he <;> linarith

lemma pseudo_correct_zero_halfLength : honestHalfLength 0 = normalCritical := by
  have hroot := (pseudo_counter_root 0).2.2
  rw [pseudo_counter_coverage_symmetric] at hroot
  norm_num only [sub_zero, add_zero] at hroot
  apply pseudo_counter_cdf_mono.injective
  rw [native_power_correction_critical_cdf]
  linarith

lemma pseudo_correct_zero_formula (t : ℝ) :
    pseudoP t (honestHalfLength 0) = 2*normalCDF (-|t|) := by
  rw [pseudo_correct_zero_halfLength, pseudoP]
  congr 2
  field_simp [native_power_correction_critical_pos.ne']

lemma pseudo_correct_zero_uniform (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    (biasModelLaw 0 0).real {t | pseudoP t (honestHalfLength 0) ≤ α} = α := by
  rw [pseudo_counter_pseudo_tail 0 _ α (pseudo_counter_root 0).2.1 hα hα1,
    pseudo_correct_zero_halfLength]
  have hz := native_power_correction_critical_pos.ne'
  have he : normalCritical*normalQuantile (1-α/2)/normalCritical =
      normalQuantile (1-α/2) := by field_simp
  rw [he, zero_sub, neg_zero, zero_sub, native_power_correction_cdf_neg,
    pseudo_counter_quantile _ (by linarith) (by linarith)]
  ring

lemma pseudo_correct_aware_coverage (B t : ℝ) :
    biasAwareP B t = 1-biasCoverage B |t| := by
  rw [pseudo_counter_tail_formula]
  rfl

lemma pseudo_correct_aware_zero (B : ℝ) : biasAwareP B 0 = 1 := by
  rw [pseudo_correct_aware_coverage, abs_zero, pseudo_counter_coverage_zero]
  norm_num

lemma pseudo_correct_aware_cont (B : ℝ) : Continuous (biasAwareP B) := by
  unfold biasAwareP
  exact (pseudo_counter_cdf_cont.comp (by fun_prop)).add
    (pseudo_counter_cdf_cont.comp (by fun_prop))

lemma pseudo_correct_aware_anti (B : ℝ) : StrictAntiOn (biasAwareP B) (Ici 0) := by
  intro x hx y hy hxy
  rw [pseudo_correct_aware_coverage, pseudo_correct_aware_coverage,
    abs_of_nonneg hy, abs_of_nonneg hx]
  have hh := pseudo_counter_coverage_mono B hxy
  linarith

lemma pseudo_correct_aware_limit (B : ℝ) : Tendsto (biasAwareP B) atTop (𝓝 0) := by
  have ha : Tendsto (fun x : ℝ => |x|) atTop atTop := by
    apply tendsto_atTop_mono (fun x => le_abs_self x) tendsto_id
  have ht := (pseudo_counter_coverage_limit B).comp ha
  have he : biasAwareP B = fun x => 1-biasCoverage B |x| := by
    funext x
    exact pseudo_correct_aware_coverage B x
  rw [he]
  simpa only [sub_self] using (tendsto_const_nhds.sub ht :
    Tendsto (fun x : ℝ => 1-biasCoverage B |x|) atTop (𝓝 (1-1)))

lemma pseudo_correct_aware_cutoff (B α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧ biasAwareP B c = α := by
  obtain ⟨K, hK, hK1⟩ := (((pseudo_correct_aware_limit B).eventually
    (eventually_lt_nhds hα)).and (eventually_ge_atTop (1:ℝ))).exists
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨c, hc, he⟩ := intermediate_value_Icc' hK0
    (pseudo_correct_aware_cont B).continuousOn
    (show α ∈ Icc (biasAwareP B K) (biasAwareP B 0) by
      rw [pseudo_correct_aware_zero]; exact ⟨hK.le,hα1.le⟩)
  have hc0 : 0 < c := by
    by_contra hn
    have he0 : c = 0 := le_antisymm (le_of_not_gt hn) hc.1
    rw [he0, pseudo_correct_aware_zero] at he
    linarith
  exact ⟨c, hc0, he⟩

lemma pseudo_correct_aware_event (B c α : ℝ) (hc : 0 ≤ c) (he : biasAwareP B c = α) :
    {t | biasAwareP B t ≤ α} = {t | c ≤ |t|} := by
  ext t
  have heven : biasAwareP B t = biasAwareP B |t| := by simp [biasAwareP]
  simp only [mem_setOf_eq, heven, ← he]
  exact (pseudo_correct_aware_anti B).le_iff_ge (abs_nonneg t) hc

lemma pseudo_correct_aware_valid (B : ℝ) (hB : 0 ≤ B) : ValidBiasP B (biasAwareP B) := by
  intro b hb α hα hα1
  obtain ⟨c, hc, he⟩ := pseudo_correct_aware_cutoff B α hα hα1
  rw [pseudo_correct_aware_event B c α hc.le he, pseudo_counter_tail_weak b c hc]
  have hw := (pseudo_counter_worst_coverage B b c hB hb hc).1
  have ht : 1-biasCoverage B c = α := by
    simpa only [pseudo_correct_aware_coverage, abs_of_pos hc] using he
  linarith

lemma pseudo_correct_aware_boundary (B b α : ℝ) (hb : |b| = B)
    (hα : 0 < α) (hα1 : α < 1) :
    (biasModelLaw 0 b).real {t | biasAwareP B t ≤ α} = α := by
  obtain ⟨c, hc, he⟩ := pseudo_correct_aware_cutoff B α hα hα1
  rw [pseudo_correct_aware_event B c α hc.le he, pseudo_counter_tail_weak b c hc,
    ← pseudo_counter_coverage_abs b c, hb]
  simpa only [pseudo_correct_aware_coverage, abs_of_pos hc] using he

lemma pseudo_correct_aware_five_percent (B t : ℝ) :
    (biasAwareP B t ≤ 1/20 ↔ honestHalfLength B ≤ |t|) ∧
    (biasAwareP B t ≤ 1/20 ↔ pseudoP t (honestHalfLength B) ≤ 1/20) := by
  have hr := (pseudo_counter_root B).2
  have he : biasAwareP B (honestHalfLength B) = 1/20 := by
    rw [pseudo_correct_aware_coverage, abs_of_pos hr.1, hr.2]
    norm_num
  have hiff : biasAwareP B t ≤ 1/20 ↔ honestHalfLength B ≤ |t| := by
    have hs := congrArg (fun s : Set ℝ => t ∈ s)
      (pseudo_correct_aware_event B (honestHalfLength B) (1/20) hr.1.le he)
    exact Iff.of_eq hs
  exact ⟨hiff, hiff.trans (pseudo_correct_geometry t _ hr.1).2.2.2.symm⟩

theorem pseudo_p_correction_proof :
    (∀ t h : ℝ, 0 < h →
      ((|t|/(h/normalCritical)) = normalCritical*|t|/h) ∧
      (pseudoP t h < 1/20 ↔ h < |t|) ∧
      (pseudoP t h < 1/20 ↔ 0 ∉ Icc (t-h) (t+h)) ∧
      (pseudoP t h ≤ 1/20 ↔ h ≤ |t|)) ∧
    (∀ B : ℝ, 0 ≤ B → (∃! H : ℝ, 0 < H ∧ biasCoverage B H = 19/20) ∧
      0 < honestHalfLength B ∧ biasCoverage B (honestHalfLength B) = 19/20 ∧
      (∀ b : ℝ, |b| ≤ B →
        (biasModelLaw 0 b).real {t | pseudoP t (honestHalfLength B) < 1/20} =
          1-biasCoverage b (honestHalfLength B) ∧
        (biasModelLaw 0 b).real {t | pseudoP t (honestHalfLength B) < 1/20} ≤ 1/20 ∧
        ((biasModelLaw 0 b).real {t | pseudoP t (honestHalfLength B) < 1/20} = 1/20 ↔ |b| = B))) ∧
    honestHalfLength 0 = normalCritical ∧
    (∀ t : ℝ, pseudoP t (honestHalfLength 0) = 2*normalCDF (-|t|)) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      (biasModelLaw 0 0).real {t | pseudoP t (honestHalfLength 0) ≤ α} = α) ∧
    (1/5:ℝ) < (biasModelLaw 0 1).real {t | pseudoP t (honestHalfLength 1) ≤ 1/5} ∧
    (∀ B : ℝ, 0 ≤ B →
      biasAwareP B 0 = 1 ∧ Continuous (biasAwareP B) ∧
      StrictAntiOn (biasAwareP B) (Ici 0) ∧
      Tendsto (biasAwareP B) atTop (𝓝 0) ∧ ValidBiasP B (biasAwareP B) ∧
      (∀ b α : ℝ, |b| = B → 0 < α → α < 1 →
        (biasModelLaw 0 b).real {t | biasAwareP B t ≤ α} = α) ∧
      (∀ t : ℝ, (biasAwareP B t ≤ 1/20 ↔ honestHalfLength B ≤ |t|) ∧
        (biasAwareP B t ≤ 1/20 ↔ pseudoP t (honestHalfLength B) ≤ 1/20))) := by
  refine ⟨pseudo_correct_geometry, pseudo_correct_honest_size,
    pseudo_correct_zero_halfLength, pseudo_correct_zero_formula, pseudo_correct_zero_uniform,
    ?_, ?_⟩
  · linarith only [pseudo_counter_rejection_bounds.1.1]
  · intro B hB
    exact ⟨pseudo_correct_aware_zero B, pseudo_correct_aware_cont B,
      pseudo_correct_aware_anti B, pseudo_correct_aware_limit B,
      pseudo_correct_aware_valid B hB,
      fun b α hb hα hα1 => pseudo_correct_aware_boundary B b α hb hα hα1,
      pseudo_correct_aware_five_percent B⟩

end
end AronowAudit.P033.Wave1
