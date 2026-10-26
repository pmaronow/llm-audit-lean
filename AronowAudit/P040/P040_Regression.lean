import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-! P040, regression reference distributions. The deposited calculation uses
Student t as a reference; no exact null distribution for the HC1 statistic is
asserted. Exact rational squared statistics are recorded separately from the
least-squares identities that identify them with the daily-sales regressions.
-/

namespace AronowAudit.P040

set_option maxHeartbeats 2000000
open scoped BigOperators
open MeasureTheory
noncomputable section

/-- "two-tailed" and "normal approximation" (paper p.4, left column;
normal reference): p_N(q)=1-sqrt(2/pi)∫₀^sqrt(q) exp(-u²/2)du.
This is the actual normal tail integral, not a rational proxy. -/
def normalReferenceP (q : ℝ) : ℝ :=
  1 - Real.sqrt (2 / Real.pi) * ∫ u in (0 : ℝ)..Real.sqrt q, Real.exp (-u ^ 2 / 2)

/-- "f_nu(t) = Gamma((nu+1)/2)/(sqrt(nu*pi) Gamma(nu/2)) ..."
(targets S7). Student-t reference density for nu>0. -/
def studentReferenceDensity (nu t : ℝ) : ℝ :=
  Real.Gamma ((nu + 1) / 2) / (Real.sqrt (nu * Real.pi) * Real.Gamma (nu / 2)) *
    (1 + t ^ 2 / nu) ^ (-((nu + 1) / 2))

/-- "p_T(q;nu)=1-2∫₀^sqrt(q) f_nu(t)dt" (targets S7).
This specifies the reference used for p values, not the null law of a robust t statistic. -/
def studentReferenceP (q nu : ℝ) : ℝ :=
  1 - 2 * ∫ t in (0 : ℝ)..Real.sqrt q, studentReferenceDensity nu t

/-- "q_café = 12767624825803755635000/42131842162249950707521"
(T4 B1). Identification with the fitted regression is
a separate assertion; this definition records the exact witness. -/
def cafeSquaredStatistic : ℝ := 12767624825803755635000 / 42131842162249950707521

/-- "q_bulk = 12396039010057804992800/10415886991743115636339"
(T4 B2). Uses unrounded data, not 23.2/21.2. -/
def bulkSquaredStatistic : ℝ := 12396039010057804992800 / 10415886991743115636339

/-- "beta_T = -146561/16484" (T4 B1). -/
def cafeCoefficientWitness : ℝ := -146561 / 16484

/-- "v = 42131842162249950707521/161509653387533360000"
(T4 B1), the adjusted café HC1 variance witness. -/
def cafeVarianceWitness : ℝ := 42131842162249950707521 / 161509653387533360000

/-- "beta_T = 955199/41210" (T4 B2). -/
def bulkCoefficientWitness : ℝ := 955199 / 41210

/-- "v = 10415886991743115636339/23072807626790480000"
(T4 B2), the adjusted bulk HC1 variance witness. -/
def bulkVarianceWitness : ℝ := 10415886991743115636339 / 23072807626790480000

/-- Two-decimal rounding from targets S7, as applied to the printed p values
.59 and .29 (paper p.5, left column). -/
def pValueRoundsTwo (x w : ℝ) : Prop := w - 1 / 200 ≤ x ∧ x < w + 1 / 200

/-- Exact witness arithmetic in P040-T4 B1–B2: both HC1 variances are positive,
and beta_T²/v equals the specified q, with q positive and below 8/5. -/
theorem regression_witness_arithmetic :
    0 < cafeVarianceWitness ∧ 0 < bulkVarianceWitness ∧
    cafeCoefficientWitness ^ 2 / cafeVarianceWitness = cafeSquaredStatistic ∧
    bulkCoefficientWitness ^ 2 / bulkVarianceWitness = bulkSquaredStatistic ∧
    0 < cafeSquaredStatistic ∧ cafeSquaredStatistic < (8 : ℝ) / 5 ∧
    0 < bulkSquaredStatistic ∧ bulkSquaredStatistic < (8 : ℝ) / 5 := by
  norm_num [cafeVarianceWitness, bulkVarianceWitness, cafeCoefficientWitness,
    bulkCoefficientWitness, cafeSquaredStatistic, bulkSquaredStatistic]

/-- Finite Taylor polynomial for exp(-u²/2), used to certify the normal-tail
integrals of T4. The Mathlib exponential remainder estimate supplies a
two-sided error bound. -/
def normalKernelPolynomial (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 10, (-u ^ 2 / 2) ^ k / (Nat.factorial k : ℝ)

/-- Integral coefficients of the Taylor polynomial (normal reference). -/
def normalIntegratedSeries (q : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 10,
    (-1 : ℝ) ^ k * q ^ k / ((2 : ℝ) ^ k * (Nat.factorial k : ℝ) * (2 * k + 1 : ℕ))

/-- Uniform exponential remainder 11/(10!·10) for |x|≤1;
Mathlib's exp_bound, used only as an internally proved numerical certificate. -/
def normalTaylorError : ℝ := 11 / 36288000

/-- The Taylor polynomial integrates to sqrt(q) times its finite rational
series (T4 finite analytic lemma); there is no unproved series-to-integral link. -/
theorem normal_polynomial_integral {q : ℝ} (hq : 0 ≤ q) :
    (∫ u in (0 : ℝ)..Real.sqrt q, normalKernelPolynomial u) =
      Real.sqrt q * normalIntegratedSeries q := by
  let z := Real.sqrt q
  have hzsq : z ^ 2 = q := Real.sq_sqrt hq
  have hint (k : ℕ) : (∫ u in (0 : ℝ)..z, (-u ^ 2 / 2) ^ k / (Nat.factorial k : ℝ)) =
      z * ((-1 : ℝ) ^ k * q ^ k /
        ((2 : ℝ) ^ k * (Nat.factorial k : ℝ) * (2 * k + 1 : ℕ))) := by
    have he : (fun u : ℝ => (-u ^ 2 / 2) ^ k / (Nat.factorial k : ℝ)) =
        (fun u : ℝ => ((-1 : ℝ) ^ k / ((2 : ℝ) ^ k * (Nat.factorial k : ℝ))) * u ^ (2 * k)) := by
      funext u
      rw [show -u ^ 2 / 2 = ((-1 : ℝ) / 2) * u ^ 2 by ring, mul_pow, div_pow, ← pow_mul]
      ring
    rw [he, intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (by omega : 2 * k + 1 ≠ 0), sub_zero, pow_add, pow_one,
      pow_mul, hzsq]
    push_cast
    have hf0 : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    have hden : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  unfold normalKernelPolynomial normalIntegratedSeries
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact hint k
  · intro k hk
    exact (by fun_prop : Continuous (fun u : ℝ => (-u ^ 2 / 2) ^ k /
      (Nat.factorial k : ℝ))).intervalIntegrable _ _

/-- A rigorous uniform pointwise enclosure of the normal kernel on
[0,sqrt(q)], for 0≤q≤2 (T4 analytic certificate). -/
theorem normal_kernel_error {q : ℝ} (hq : 0 ≤ q) (hq2 : q ≤ 2)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) (Real.sqrt q)) :
    |Real.exp (-u ^ 2 / 2) - normalKernelPolynomial u| ≤ normalTaylorError := by
  have hs := Real.sq_sqrt hq
  have husq : u ^ 2 ≤ q := by
    have hh := (sq_le_sq₀ hu.1 (Real.sqrt_nonneg q)).mpr hu.2
    rwa [hs] at hh
  have hx : |-u ^ 2 / 2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg u]
  have hb : |Real.exp (-u ^ 2 / 2) - normalKernelPolynomial u| ≤
      |-u ^ 2 / 2| ^ 10 * normalTaylorError := by
    convert (Real.exp_bound hx (n := 10) (by norm_num)) using 1 <;>
      norm_num [normalKernelPolynomial, normalTaylorError, Nat.factorial]
  have hp : |-u ^ 2 / 2| ^ 10 ≤ 1 := by
    simpa using pow_le_pow_left₀ (abs_nonneg (-u ^ 2 / 2)) hx 10
  exact hb.trans (by nlinarith [show 0 ≤ normalTaylorError by norm_num [normalTaylorError]])

/-- Integration preserves the uniform Taylor enclosure (T4), giving a proved
finite approximation with explicit error on either side of the actual normal integral. -/
theorem normal_integral_enclosure {q : ℝ} (hq : 0 ≤ q) (hq2 : q ≤ 2) :
    Real.sqrt q * (normalIntegratedSeries q - normalTaylorError) ≤
      (∫ u in (0 : ℝ)..Real.sqrt q, Real.exp (-u ^ 2 / 2)) ∧
    (∫ u in (0 : ℝ)..Real.sqrt q, Real.exp (-u ^ 2 / 2)) ≤
      Real.sqrt q * (normalIntegratedSeries q + normalTaylorError) := by
  have hf : Continuous (fun u : ℝ => Real.exp (-u ^ 2 / 2)) := by fun_prop
  have hp : Continuous normalKernelPolynomial := by unfold normalKernelPolynomial; fun_prop
  have hlo : Continuous (fun u => normalKernelPolynomial u - normalTaylorError) := by fun_prop
  have hhi : Continuous (fun u => normalKernelPolynomial u + normalTaylorError) := by fun_prop
  have hl := intervalIntegral.integral_mono_on (μ := volume) (Real.sqrt_nonneg q)
    (hlo.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
    (fun u hu => by have h := (abs_le.mp (normal_kernel_error hq hq2 hu)).1; linarith)
  have hh := intervalIntegral.integral_mono_on (μ := volume) (Real.sqrt_nonneg q)
    (hf.intervalIntegrable _ _) (hhi.intervalIntegrable _ _)
    (fun u hu => by have h := (abs_le.mp (normal_kernel_error hq hq2 hu)).2; linarith)
  rw [intervalIntegral.integral_sub (hp.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const, normal_polynomial_integral hq] at hl
  rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const, normal_polynomial_integral hq] at hh
  simp only [sub_zero, smul_eq_mul] at hl hh
  constructor <;> nlinarith

/-- The actual normal p value lies in the Taylor enclosure after normalization
(T4). The square-root multiplier remains the mathematical one involving π. -/
theorem normal_p_enclosure {q : ℝ} (hq : 0 ≤ q) (hq2 : q ≤ 2) :
    1 - Real.sqrt (2 * q / Real.pi) * (normalIntegratedSeries q + normalTaylorError) ≤
      normalReferenceP q ∧
    normalReferenceP q ≤
      1 - Real.sqrt (2 * q / Real.pi) * (normalIntegratedSeries q - normalTaylorError) := by
  have hc : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have he := normal_integral_enclosure hq hq2
  have hm : Real.sqrt (2 / Real.pi) * Real.sqrt q = Real.sqrt (2 * q / Real.pi) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 / Real.pi)]
    congr 1
    ring
  have hl := mul_le_mul_of_nonneg_left he.1 hc
  have hh := mul_le_mul_of_nonneg_left he.2 hc
  rw [← mul_assoc, hm] at hl hh
  unfold normalReferenceP
  constructor <;> linarith

/-- A small rational certificate suffices to turn the proved analytic enclosure
into decimal bounds (T4). All hypotheses are finite rational inequalities when
q and the supplied endpoints are rational; the π bounds come from Mathlib. -/
theorem normal_decimal_certificate {q alo ahi plo phi : ℝ}
    (hq : 0 ≤ q) (hq2 : q ≤ 2) (halopos : 0 ≤ alo) (hahipos : 0 ≤ ahi)
    (halosq : alo ^ 2 * (3141593 / 1000000 : ℝ) < 2 * q)
    (hahisq : 2 * q < ahi ^ 2 * (3141592 / 1000000 : ℝ))
    (hs : 0 ≤ normalIntegratedSeries q - normalTaylorError)
    (hplo : plo < 1 - ahi * (normalIntegratedSeries q + normalTaylorError))
    (hphi : 1 - alo * (normalIntegratedSeries q - normalTaylorError) < phi) :
    plo < normalReferenceP q ∧ normalReferenceP q < phi := by
  have hpiLo : (3141592 / 1000000 : ℝ) ≤ Real.pi := by
    convert Real.pi_gt_d6.le using 1 <;> norm_num
  have hpiHi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    convert Real.pi_lt_d6.le using 1 <;> norm_num
  have haLo : alo < Real.sqrt (2 * q / Real.pi) := by
    apply (Real.lt_sqrt halopos).mpr
    apply (lt_div_iff₀ Real.pi_pos).mpr
    exact (mul_le_mul_of_nonneg_left hpiHi (sq_nonneg alo)).trans_lt halosq
  have haHi : Real.sqrt (2 * q / Real.pi) < ahi := by
    apply (Real.sqrt_lt (by positivity) hahipos).mpr
    apply (div_lt_iff₀ Real.pi_pos).mpr
    exact hahisq.trans_le (mul_le_mul_of_nonneg_left hpiLo (sq_nonneg ahi))
  have he := normal_p_enclosure hq hq2
  have herr : 0 ≤ normalTaylorError := by norm_num [normalTaylorError]
  have hsplus : 0 ≤ normalIntegratedSeries q + normalTaylorError := by linarith
  have hmhi := mul_le_mul_of_nonneg_right haHi.le hsplus
  have hmlo := mul_le_mul_of_nonneg_right haLo.le hs
  constructor <;> linarith [he.1, he.2]

/-- P040-T4 B3–B4: rigorous decimal enclosures of the actual normal-reference
tail integrals for the two exact squared statistics. Identifying
these rationals with the regressions is stated separately. -/
theorem normal_reference_counterexample_bounds :
    (58198 / 100000 : ℝ) < normalReferenceP cafeSquaredStatistic ∧
    normalReferenceP cafeSquaredStatistic < (58199 / 100000 : ℝ) ∧
    (27530 / 100000 : ℝ) < normalReferenceP bulkSquaredStatistic ∧
    normalReferenceP bulkSquaredStatistic < (27531 / 100000 : ℝ) := by
  have hc := normal_decimal_certificate (q := cafeSquaredStatistic)
    (alo := 4392278 / 10000000) (ahi := 4392280 / 10000000)
    (plo := 58198 / 100000) (phi := 58199 / 100000)
    (by norm_num [cafeSquaredStatistic]) (by norm_num [cafeSquaredStatistic])
    (by norm_num) (by norm_num)
    (by norm_num [cafeSquaredStatistic]) (by norm_num [cafeSquaredStatistic])
    (by norm_num [normalIntegratedSeries, Finset.sum_range_succ, cafeSquaredStatistic,
      normalTaylorError, Nat.factorial])
    (by norm_num [normalIntegratedSeries, Finset.sum_range_succ, cafeSquaredStatistic,
      normalTaylorError, Nat.factorial])
    (by norm_num [normalIntegratedSeries, Finset.sum_range_succ, cafeSquaredStatistic,
      normalTaylorError, Nat.factorial])
  have hb := normal_decimal_certificate (q := bulkSquaredStatistic)
    (alo := 8704290 / 10000000) (ahi := 8704292 / 10000000)
    (plo := 27530 / 100000) (phi := 27531 / 100000)
    (by norm_num [bulkSquaredStatistic]) (by norm_num [bulkSquaredStatistic])
    (by norm_num) (by norm_num)
    (by norm_num [bulkSquaredStatistic]) (by norm_num [bulkSquaredStatistic])
    (by norm_num [normalIntegratedSeries, Finset.sum_range_succ, bulkSquaredStatistic,
      normalTaylorError, Nat.factorial])
    (by norm_num [normalIntegratedSeries, Finset.sum_range_succ, bulkSquaredStatistic,
      normalTaylorError, Nat.factorial])
    (by norm_num [normalIntegratedSeries, Finset.sum_range_succ, bulkSquaredStatistic,
      normalTaylorError, Nat.factorial])
  exact ⟨hc.1, hc.2, hb.1, hb.2⟩

/-- P040-T4 consequence/T5(iv): the normal-reference values round to .58 and
.28 and cannot round to the paper's .59 and .29. -/
theorem normal_reference_rounding_mismatch :
    pValueRoundsTwo (normalReferenceP cafeSquaredStatistic) (58 / 100) ∧
    ¬pValueRoundsTwo (normalReferenceP cafeSquaredStatistic) (59 / 100) ∧
    pValueRoundsTwo (normalReferenceP bulkSquaredStatistic) (28 / 100) ∧
    ¬pValueRoundsTwo (normalReferenceP bulkSquaredStatistic) (29 / 100) := by
  have h := normal_reference_counterexample_bounds
  unfold pValueRoundsTwo
  refine ⟨⟨by linarith [h.1], by linarith [h.2.1]⟩, ?_,
    ⟨by linarith [h.2.2.1], by linarith [h.2.2.2]⟩, ?_⟩
  · intro hh; linarith [hh.1, h.2.1]
  · intro hh; linarith [hh.1, h.2.2.2]

/-- "f_21(t) = 4^10/(pi choose(20,10) sqrt(21)) (1+t²/21)^(-11)"
(T5(ii)). Integer-power form for the same Student-t density. -/
def student21Density (t : ℝ) : ℝ :=
  (4 : ℝ) ^ 10 / (Real.pi * (Nat.choose 20 10 : ℝ) * Real.sqrt 21) /
    (1 + t ^ 2 / 21) ^ 11

/-- The general Gamma-function reference density at ν=21 equals the special
integer-power density of T5(ii); the normalizing constant is proved in Lean. -/
theorem student21_density_identity (t : ℝ) :
    studentReferenceDensity 21 t = student21Density t := by
  have hg11 : Real.Gamma 11 = (3628800 : ℝ) := by
    convert Real.Gamma_nat_eq_factorial 10 using 1 <;> norm_num [Nat.factorial]
  have hghalf : Real.Gamma (21 / 2) = (654729075 : ℝ) * Real.sqrt Real.pi / 1024 := by
    convert Real.Gamma_nat_add_half 10 using 1 <;> norm_num [Nat.doubleFactorial]
  have hbase : 0 < 1 + t ^ 2 / 21 := by positivity
  have hsqpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hs21 : Real.sqrt (21 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hspi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold studentReferenceDensity student21Density
  norm_num [hg11, hghalf, Real.rpow_neg, Real.rpow_natCast, Nat.choose]
  field_simp [Real.pi_ne_zero, hs21, hspi, hbase.ne']
  nlinarith [hsqpi]

/-- Finite polynomial of degree n in the binomial expansion of (1+x)^(-11)
(Student-t reference). A polynomial remainder certificate,
rather than an assumed infinite-series identity, supplies the bounds below. -/
def student21Taylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (Nat.choose (10 + k) k : ℝ) * x ^ k

/-- The integrated coefficients of the Student-t polynomial certificate
(Student-t reference). -/
def student21IntegratedSeries (n : ℕ) (q : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ k * (Nat.choose (10 + k) k : ℝ) * (q / 21) ^ k / (2 * k + 1 : ℕ)

/-- "A = 2 * 4^10 / choose(20,10)" (Student-t reference). -/
def student21Scale : ℝ := 2 * (4 : ℝ) ^ 10 / (Nat.choose 20 10 : ℝ)

/-- Rigorous polynomial bounds for the Student-t(21) kernel (T5(ii)).
Multiplying by (1+x)^11 leaves polynomials with positive coefficients. -/
theorem student21_kernel_bracket {x : ℝ} (hx : 0 ≤ x) :
    student21Taylor 11 x ≤ 1 / (1 + x) ^ 11 ∧
    1 / (1 + x) ^ 11 ≤ student21Taylor 10 x := by
  have hu : (1 + x) ^ 11 * student21Taylor 10 x - 1 = x ^ 11 *
      (352716 + 3233230 * x ^ 1 + 13430340 * x ^ 2 + 33256080 * x ^ 3 + 54318264 * x ^ 4 + 61108047 * x ^ 5 + 47927880 * x ^ 6 + 25865840 * x ^ 7 + 9189180 * x ^ 8 + 1939938 * x ^ 9 + 184756 * x ^ 10) := by
    norm_num [student21Taylor, Finset.sum_range_succ, Nat.choose]
    ring
  have hl : 1 - (1 + x) ^ 11 * student21Taylor 11 x = x ^ 12 *
      (646646 + 5969040 * x ^ 1 + 24942060 * x ^ 2 + 62078016 * x ^ 3 + 101846745 * x ^ 4 + 115026912 * x ^ 5 + 90530440 * x ^ 6 + 49008960 * x ^ 7 + 17459442 * x ^ 8 + 3695120 * x ^ 9 + 352716 * x ^ 10) := by
    norm_num [student21Taylor, Finset.sum_range_succ, Nat.choose]
    ring
  have hup : 0 ≤ x ^ 11 * (352716 + 3233230 * x ^ 1 + 13430340 * x ^ 2 + 33256080 * x ^ 3 + 54318264 * x ^ 4 + 61108047 * x ^ 5 + 47927880 * x ^ 6 + 25865840 * x ^ 7 + 9189180 * x ^ 8 + 1939938 * x ^ 9 + 184756 * x ^ 10) := by positivity
  have hlp : 0 ≤ x ^ 12 * (646646 + 5969040 * x ^ 1 + 24942060 * x ^ 2 + 62078016 * x ^ 3 + 101846745 * x ^ 4 + 115026912 * x ^ 5 + 90530440 * x ^ 6 + 49008960 * x ^ 7 + 17459442 * x ^ 8 + 3695120 * x ^ 9 + 352716 * x ^ 10) := by positivity
  have hden : 0 < (1 + x) ^ 11 := pow_pos (by linarith) _
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith [hl]
  · apply (div_le_iff₀ hden).mpr
    nlinarith [hu]

/-- The Student-t(21) polynomial bounds integrate to their explicit finite
series (T5(ii)); this connects the numerical certificates to actual integrals. -/
theorem student21_polynomial_integral (n : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (∫ u in (0 : ℝ)..Real.sqrt q, student21Taylor n (u ^ 2 / 21)) =
      Real.sqrt q * student21IntegratedSeries n q := by
  let z := Real.sqrt q
  have hsq : z ^ 2 = q := Real.sq_sqrt hq
  have hint (k : ℕ) :
      (∫ u in (0 : ℝ)..z, (-1 : ℝ) ^ k * (Nat.choose (10 + k) k : ℝ) * (u ^ 2 / 21) ^ k) =
        z * ((-1 : ℝ) ^ k * (Nat.choose (10 + k) k : ℝ) * (q / 21) ^ k / (2 * k + 1 : ℕ)) := by
    have he : (fun u : ℝ => (-1 : ℝ) ^ k * (Nat.choose (10 + k) k : ℝ) * (u ^ 2 / 21) ^ k) =
        (fun u : ℝ => ((-1 : ℝ) ^ k * (Nat.choose (10 + k) k : ℝ) / (21 : ℝ) ^ k) * u ^ (2 * k)) := by
      funext u
      rw [div_pow, ← pow_mul]
      ring
    rw [he, intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (by omega : 2 * k + 1 ≠ 0), sub_zero, pow_add, pow_one,
      pow_mul, hsq, div_pow]
    push_cast
    have hden : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  unfold student21Taylor student21IntegratedSeries
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact hint k
  · intro k hk
    exact (by fun_prop : Continuous (fun u : ℝ => (-1 : ℝ) ^ k *
      (Nat.choose (10 + k) k : ℝ) * (u ^ 2 / 21) ^ k)).intervalIntegrable _ _

/-- A proved two-sided enclosure of the actual Student-t(21) reference p value
(T5(ii)), with the Gamma normalization and integration links included. -/
theorem student21_p_enclosure {q : ℝ} (hq : 0 ≤ q) :
    1 - (student21Scale * Real.sqrt (q / 21) / Real.pi) * student21IntegratedSeries 10 q ≤
      studentReferenceP q 21 ∧
    studentReferenceP q 21 ≤
      1 - (student21Scale * Real.sqrt (q / 21) / Real.pi) * student21IntegratedSeries 11 q := by
  let C := (4 : ℝ) ^ 10 / (Real.pi * (Nat.choose 20 10 : ℝ) * Real.sqrt 21)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hkernel : Continuous (fun t : ℝ => 1 / (1 + t ^ 2 / 21) ^ 11) := by
    exact continuous_const.div (by fun_prop) (fun t =>
      (pow_pos (by positivity : (0 : ℝ) < 1 + t ^ 2 / 21) 11).ne')
  have hT10 : Continuous (fun t : ℝ => student21Taylor 10 (t ^ 2 / 21)) := by
    unfold student21Taylor; fun_prop
  have hT11 : Continuous (fun t : ℝ => student21Taylor 11 (t ^ 2 / 21)) := by
    unfold student21Taylor; fun_prop
  have hl := intervalIntegral.integral_mono_on (μ := volume) (Real.sqrt_nonneg q)
    (hT11.intervalIntegrable _ _) (hkernel.intervalIntegrable _ _)
    (fun t ht => (student21_kernel_bracket (by positivity : 0 ≤ t ^ 2 / 21)).1)
  have hh := intervalIntegral.integral_mono_on (μ := volume) (Real.sqrt_nonneg q)
    (hkernel.intervalIntegrable _ _) (hT10.intervalIntegrable _ _)
    (fun t ht => (student21_kernel_bracket (by positivity : 0 ≤ t ^ 2 / 21)).2)
  rw [student21_polynomial_integral 11 hq] at hl
  rw [student21_polynomial_integral 10 hq] at hh
  have hP : studentReferenceP q 21 =
      1 - (2 * C) * (∫ t in (0 : ℝ)..Real.sqrt q, 1 / (1 + t ^ 2 / 21) ^ 11) := by
    unfold studentReferenceP
    simp_rw [student21_density_identity]
    have he : student21Density = (fun t : ℝ => C * (1 / (1 + t ^ 2 / 21) ^ 11)) := by
      funext t; dsimp [student21Density, C]; ring
    rw [he, intervalIntegral.integral_const_mul]
    ring
  have hm : (2 * C) * Real.sqrt q = student21Scale * Real.sqrt (q / 21) / Real.pi := by
    rw [Real.sqrt_div hq]
    dsimp [C, student21Scale]
    ring
  have hcl := mul_le_mul_of_nonneg_left hl (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
  have hch := mul_le_mul_of_nonneg_left hh (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
  rw [← mul_assoc, hm] at hcl hch
  rw [hP]
  constructor <;> linarith

/-- Rational decimal-certificate wrapper for Student-t(21) probabilities
(T5(ii)). The analytic enclosure is a theorem, not a named numerical axiom. -/
theorem student21_decimal_certificate {q alo ahi plo phi : ℝ}
    (hq : 0 ≤ q) (halopos : 0 ≤ alo) (hahipos : 0 ≤ ahi)
    (halosq : alo ^ 2 * (3141593 / 1000000 : ℝ) ^ 2 < student21Scale ^ 2 * (q / 21))
    (hahisq : student21Scale ^ 2 * (q / 21) < ahi ^ 2 * (3141592 / 1000000 : ℝ) ^ 2)
    (hs11 : 0 ≤ student21IntegratedSeries 11 q) (hs10 : 0 ≤ student21IntegratedSeries 10 q)
    (hplo : plo < 1 - ahi * student21IntegratedSeries 10 q)
    (hphi : 1 - alo * student21IntegratedSeries 11 q < phi) :
    plo < studentReferenceP q 21 ∧ studentReferenceP q 21 < phi := by
  let B := student21Scale * Real.sqrt (q / 21) / Real.pi
  have hB0 : 0 ≤ B := by dsimp [B, student21Scale]; positivity
  have hBsq : B ^ 2 * Real.pi ^ 2 = student21Scale ^ 2 * (q / 21) := by
    dsimp [B]
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), mul_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q / 21)]
  have hpiLo : (3141592 / 1000000 : ℝ) ≤ Real.pi := by
    convert Real.pi_gt_d6.le using 1 <;> norm_num
  have hpiHi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    convert Real.pi_lt_d6.le using 1 <;> norm_num
  have hpiSqLo : (3141592 / 1000000 : ℝ) ^ 2 ≤ Real.pi ^ 2 :=
    (sq_le_sq₀ (by norm_num) Real.pi_pos.le).mpr hpiLo
  have hpiSqHi : Real.pi ^ 2 ≤ (3141593 / 1000000 : ℝ) ^ 2 :=
    (sq_le_sq₀ Real.pi_pos.le (by norm_num)).mpr hpiHi
  have haLo : alo < B := by
    have hh : alo ^ 2 * Real.pi ^ 2 < B ^ 2 * Real.pi ^ 2 := by
      rw [hBsq]
      exact (mul_le_mul_of_nonneg_left hpiSqHi (sq_nonneg alo)).trans_lt halosq
    have hsq := (mul_lt_mul_iff_of_pos_right (sq_pos_of_pos Real.pi_pos)).mp hh
    nlinarith
  have haHi : B < ahi := by
    have hh : B ^ 2 * Real.pi ^ 2 < ahi ^ 2 * Real.pi ^ 2 := by
      rw [hBsq]
      exact hahisq.trans_le (mul_le_mul_of_nonneg_left hpiSqLo (sq_nonneg ahi))
    have hsq := (mul_lt_mul_iff_of_pos_right (sq_pos_of_pos Real.pi_pos)).mp hh
    nlinarith
  have he := student21_p_enclosure hq
  change 1 - B * student21IntegratedSeries 10 q ≤ _ ∧ _ ≤ 1 - B * student21IntegratedSeries 11 q at he
  have hmhi := mul_le_mul_of_nonneg_right haHi.le hs10
  have hmlo := mul_le_mul_of_nonneg_right haLo.le hs11
  constructor <;> linarith [he.1, he.2]

/-- P040-T5(ii): the corrected Student-t reference with 21 residual degrees
of freedom has the stated narrow decimal brackets for the two exact q values. -/
theorem corrected_student_reference_bounds :
    (58779 / 100000 : ℝ) < studentReferenceP cafeSquaredStatistic 21 ∧
    studentReferenceP cafeSquaredStatistic 21 < (58780 / 100000 : ℝ) ∧
    (28766 / 100000 : ℝ) < studentReferenceP bulkSquaredStatistic 21 ∧
    studentReferenceP bulkSquaredStatistic 21 < (28767 / 100000 : ℝ) := by
  have hc := student21_decimal_certificate (q := cafeSquaredStatistic)
    (alo := 4340318 / 10000000) (ahi := 4340321 / 10000000)
    (plo := 58779 / 100000) (phi := 58780 / 100000)
    (by norm_num [cafeSquaredStatistic]) (by norm_num) (by norm_num)
    (by norm_num [student21Scale, Nat.choose, cafeSquaredStatistic])
    (by norm_num [student21Scale, Nat.choose, cafeSquaredStatistic])
    (by norm_num [student21IntegratedSeries, Finset.sum_range_succ, Nat.choose, cafeSquaredStatistic])
    (by norm_num [student21IntegratedSeries, Finset.sum_range_succ, Nat.choose, cafeSquaredStatistic])
    (by norm_num [student21IntegratedSeries, Finset.sum_range_succ, Nat.choose, cafeSquaredStatistic])
    (by norm_num [student21IntegratedSeries, Finset.sum_range_succ, Nat.choose, cafeSquaredStatistic])
  have hb := student21_decimal_certificate (q := bulkSquaredStatistic)
    (alo := 8601320 / 10000000) (ahi := 8601324 / 10000000)
    (plo := 28766 / 100000) (phi := 28767 / 100000)
    (by norm_num [bulkSquaredStatistic]) (by norm_num) (by norm_num)
    (by norm_num [student21Scale, Nat.choose, bulkSquaredStatistic])
    (by norm_num [student21Scale, Nat.choose, bulkSquaredStatistic])
    (by norm_num [student21IntegratedSeries, Finset.sum_range_succ, Nat.choose, bulkSquaredStatistic])
    (by norm_num [student21IntegratedSeries, Finset.sum_range_succ, Nat.choose, bulkSquaredStatistic])
    (by norm_num [student21IntegratedSeries, Finset.sum_range_succ, Nat.choose, bulkSquaredStatistic])
    (by norm_num [student21IntegratedSeries, Finset.sum_range_succ, Nat.choose, bulkSquaredStatistic])
  exact ⟨hc.1, hc.2, hb.1, hb.2⟩

/-- P040-T5(ii): the Student-t(21) values round to the paper's .59 and .29,
in contrast to the alternative normal-reference correction. -/
theorem corrected_student_reference_rounding :
    pValueRoundsTwo (studentReferenceP cafeSquaredStatistic 21) (59 / 100) ∧
    pValueRoundsTwo (studentReferenceP bulkSquaredStatistic 21) (29 / 100) := by
  have h := corrected_student_reference_bounds
  unfold pValueRoundsTwo
  exact ⟨⟨by linarith [h.1], by linarith [h.2.1]⟩,
    ⟨by linarith [h.2.2.1], by linarith [h.2.2.2]⟩⟩

/-- "one for each ... days ... (there is no row for day 5)" (targets S6(d), deposited daily sales). Exact 30 day numbers, not a claim about how many days were assigned. -/
def salesDay : Fin 30 → ℕ :=
  ![1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

/-- "chocolate scent dispersion (treatment) and no scent (control)" (paper p.3, left). Recorded assignments from the 30 rows of targets S6(d). -/
def salesTreatment : Fin 30 → ℝ :=
  ![0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1]

/-- "book sales" (paper p.3, left; Table 1 p.5), in CAD. Exact decimal daily outcomes from targets S6(d), represented by rationals in ℝ. -/
def salesBook : Fin 30 → ℝ :=
  ![18171 / 100, 2687 / 20, 3271 / 20, 1713 / 20, 1419 / 10, 171, 1199 / 10, 1338 / 5, 5803 / 20, 168, 4981 / 20, 4511 / 20, 1293 / 10, 982 / 5, 801 / 4, 10589 / 25, 739 / 4, 3573 / 20, 839 / 10, 2647 / 20, 2241 / 20, 2413 / 20, 9019 / 20, 523 / 4, 387 / 4, 1679 / 10, 719 / 5, 200, 443 / 5, 738 / 5]

/-- "café sales (pastries, coffee, and tea)" (paper p.3, left; Table 1 p.5), in CAD. Exact decimal daily outcomes from targets S6(d). -/
def salesCafe : Fin 30 → ℝ :=
  ![9838 / 25, 36757 / 100, 5867 / 20, 5048 / 25, 29321 / 100, 30503 / 100, 10524 / 25, 7572 / 25, 38119 / 100, 5051 / 20, 29613 / 100, 8559 / 20, 8971 / 25, 34107 / 100, 16459 / 50, 7773 / 25, 24609 / 100, 31499 / 100, 6391 / 20, 36247 / 100, 389, 16343 / 50, 40049 / 100, 233, 359, 329, 349, 10711 / 25, 33407 / 100, 286]

/-- "bulk sales (primarily coffee beans, but also loose tea and spices)" (paper p.3, left; Table 1 p.5), in CAD. Exact decimals from targets S6(d). -/
def salesBulk : Fin 30 → ℝ :=
  ![421 / 5, 1623 / 20, 2001 / 20, 341 / 20, 10271 / 100, 6919 / 100, 1963 / 20, 3207 / 20, 17251 / 100, 99 / 5, 5549 / 100, 18031 / 100, 4008 / 25, 2899 / 50, 4051 / 50, 647 / 20, 2541 / 50, 154 / 5, 3059 / 25, 1247 / 25, 3831 / 50, 849 / 20, 1517 / 10, 1261 / 20, 12013 / 100, 381 / 20, 5991 / 100, 2853 / 25, 2497 / 100, 2703 / 25]

/-- "total sales" (paper p.4; Table 1 p.5). Each recorded daily total is
book + café + bulk (targets S6(b,d)); the total outcome reuses these components. -/
def salesTotal (i : Fin 30) : ℝ := salesBook i + salesCafe i + salesBulk i

/-- "four outcomes: total sales, bulk sales, café sales, and book sales"
(paper pp.3–4; Table 1 p.5), ordered accordingly. -/
def tableOutcome : Fin 4 → Fin 30 → ℝ := ![salesTotal, salesBulk, salesCafe, salesBook]

/-- "mean-centered linear time trend" (paper pp.3–4, Table 1 note p.5).
The mean is the mean of the 30 observed day numbers (targets S7). -/
def meanSalesDay : ℝ := (∑ i : Fin 30, (salesDay i : ℝ)) / 30

/-- The mean of "fixed effects for the day of week, all mean-centered"
(Table 1 note p.5), with the script's day modulo 7 coding (targets S6(c), S7). -/
def weekdayFrequency (c : Fin 7) : ℝ :=
  (∑ i : Fin 30, if salesDay i % 7 = c.val then (1 : ℝ) else 0) / 30

/-- The centered weekday indicator of targets S7 (script implementing the
paper's mean-centered day-of-week fixed effects, Table 1 note p.5). -/
def centeredWeekday (c : Fin 7) (i : Fin 30) : ℝ :=
  (if salesDay i % 7 = c.val then (1 : ℝ) else 0) - weekdayFrequency c

/-- "lm(y ~ Treat)" (targets S6(c)), implementing the unadjusted OLS
analysis described on paper pp.3–4. Rows are (1,T). -/
def unadjustedDesign : Matrix (Fin 30) (Fin 2) ℝ :=
  fun i => ![1, salesTreatment i]

/-- "X^a ... nine columns" (targets S7), implementing the mean-centered
linear time trend and weekday effects (paper pp.3–4, Table 1 note p.5).
The script's aliased seventh centered indicator is omitted here. -/
def adjustedDesign : Matrix (Fin 30) (Fin 9) ℝ :=
  fun i => ![1, salesTreatment i, (salesDay i : ℝ) - meanSalesDay,
    centeredWeekday 0 i, centeredWeekday 1 i, centeredWeekday 2 i,
    centeredWeekday 3 i, centeredWeekday 4 i, centeredWeekday 5 i]

/-- The original script's "ten columns ... and seven centred indicators"
(T5(i), targets S6(c), S7). The alias is retained to state its rank. -/
def originalAdjustedDesign : Matrix (Fin 30) (Fin 10) ℝ :=
  fun i => ![1, salesTreatment i, (salesDay i : ℝ) - meanSalesDay,
    centeredWeekday 0 i, centeredWeekday 1 i, centeredWeekday 2 i,
    centeredWeekday 3 i, centeredWeekday 4 i, centeredWeekday 5 i, centeredWeekday 6 i]

/-- P040-T5(i): the day mean and weekday frequencies of the 30 deposited rows.
These are exact finite sums over the recorded observations. -/
theorem recorded_day_summary : meanSalesDay = (491 : ℝ) / 30 ∧
    ∀ c : Fin 7, weekdayFrequency c = (![4,5,5,5,4,3,4] c : ℝ) / 30 := by
  constructor
  · norm_num [meanSalesDay, salesDay, Fin.sum_univ_succ]
  · intro c
    fin_cases c <;>
      simp only [weekdayFrequency, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> norm_num [salesDay]

/-- P040-T5(i): the unadjusted design has independent columns. -/
theorem unadjusted_columns_independent : Function.Injective unadjustedDesign.mulVecLin := by
  intro v w h
  have h0 := congrFun h (0 : Fin 30)
  have h2 := congrFun h (2 : Fin 30)
  norm_num [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, unadjustedDesign,
    salesTreatment, Fin.sum_univ_succ] at h0 h2
  funext j
  fin_cases j
  · exact h0
  · change v 1 = w 1
    linarith

/-- P040-T5(i): the nine-column adjusted design has independent columns.
Three days in the same weekday identify the treatment/time coefficients;
the remaining weekdays then identify each centered effect and intercept. -/
theorem adjusted_columns_independent : Function.Injective adjustedDesign.mulVecLin := by
  intro v w h

  have h0 := congrFun h (0 : Fin 30)

  have h6 := congrFun h (6 : Fin 30)

  have h13 := congrFun h (13 : Fin 30)

  have h5 := congrFun h (5 : Fin 30)

  have h1 := congrFun h (1 : Fin 30)

  have h2 := congrFun h (2 : Fin 30)

  have h3 := congrFun h (3 : Fin 30)

  have h10 := congrFun h (10 : Fin 30)

  have h4 := congrFun h (4 : Fin 30)

  norm_num [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, adjustedDesign,
    centeredWeekday, recorded_day_summary.1, recorded_day_summary.2,
    salesDay, salesTreatment, Fin.sum_univ_succ] at h0 h6 h13 h5 h1 h2 h3 h10 h4

  have htime : v 2 = w 2 := by linarith only [h0, h13]
  have htreat : v 1 = w 1 := by linarith only [h0, h6, htime]

  have hc3 : v 3 = w 3 := by linarith only [h5, h4, htime, htreat]

  have hc4 : v 4 = w 4 := by linarith only [h0, h4, htime, htreat]

  have hc5 : v 5 = w 5 := by linarith only [h1, h4, htime, htreat]

  have hc6 : v 6 = w 6 := by linarith only [h2, h4, htime, htreat]

  have hc7 : v 7 = w 7 := by linarith only [h3, h4, htime, htreat]

  have hc8 : v 8 = w 8 := by linarith only [h10, h4, htime, htreat]

  have hconst : v 0 = w 0 := by linarith only [h4, htime, htreat, hc3, hc4, hc5, hc6, hc7, hc8]
  funext j
  fin_cases j <;> assumption


/-- P040-T5(i): seven centered weekday indicators sum to zero in every row,
explaining the original ten-column design's alias. -/
theorem centered_weekdays_sum_zero (i : Fin 30) :
    (∑ c : Fin 7, centeredWeekday c i) = 0 := by
  fin_cases i <;> simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [centeredWeekday, recorded_day_summary.2, salesDay]

/-- P040-T5(i): deleting the seventh centered weekday indicator preserves
exactly the space of fitted values; it does not change the treatment estimand. -/
theorem adjusted_design_same_range :
    LinearMap.range originalAdjustedDesign.mulVecLin = LinearMap.range adjustedDesign.mulVecLin := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨![v 0, v 1, v 2, v 3 - v 9, v 4 - v 9, v 5 - v 9,
      v 6 - v 9, v 7 - v 9, v 8 - v 9], ?_⟩
    funext i
    have hc := centered_weekdays_sum_zero i
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
    change centeredWeekday 0 i + (centeredWeekday 1 i + (centeredWeekday 2 i +
      (centeredWeekday 3 i + (centeredWeekday 4 i + (centeredWeekday 5 i + centeredWeekday 6 i))))) = 0 at hc
    have hlast : centeredWeekday 6 i = -(centeredWeekday 0 i + centeredWeekday 1 i +
        centeredWeekday 2 i + centeredWeekday 3 i + centeredWeekday 4 i + centeredWeekday 5 i) := by
      linarith [hc]
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, originalAdjustedDesign,
      adjustedDesign, Fin.sum_univ_succ]
    rw [hlast]
    ring
  · rintro ⟨v, rfl⟩
    refine ⟨![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, 0], ?_⟩
    funext i
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, originalAdjustedDesign,
      adjustedDesign, Fin.sum_univ_succ]

/-- P040-T5(i): N=30, ranks 2 and 9, and the original ten-column matrix also
has rank 9. The residual degrees of freedom are consequently 28 and 21. -/
theorem corrected_regression_degrees_of_freedom :
    Fintype.card (Fin 30) = 30 ∧ unadjustedDesign.rank = 2 ∧ adjustedDesign.rank = 9 ∧
    originalAdjustedDesign.rank = 9 ∧
    30 - unadjustedDesign.rank = 28 ∧ 30 - originalAdjustedDesign.rank = 21 := by
  have hu : unadjustedDesign.rank = 2 := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj unadjusted_columns_independent]
    simp
  have ha : adjustedDesign.rank = 9 := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj adjusted_columns_independent]
    simp
  have ho : originalAdjustedDesign.rank = 9 := by
    rw [Matrix.rank, adjusted_design_same_range]
    exact ha
  exact ⟨by simp, hu, ha, ho, by rw [hu], by rw [ho]⟩

/-- "G=(XᵀX)^(-1) Xᵀ" (targets S7), the OLS
operator for the recorded daily-sales outcomes. Used with full-column-rank designs. -/
def olsOperator {K : ℕ} (X : Matrix (Fin 30) (Fin K) ℝ) : Matrix (Fin K) (Fin 30) ℝ :=
  (X.transpose * X)⁻¹ * X.transpose

/-- "beta_hat=Gy" (targets S7), OLS coefficients. -/
def olsCoefficients {K : ℕ} (X : Matrix (Fin 30) (Fin K) ℝ) (y : Fin 30 → ℝ) : Fin K → ℝ :=
  (olsOperator X).mulVec y

/-- "e=y-X beta_hat" (targets S7), OLS residuals. -/
def olsResidual {K : ℕ} (X : Matrix (Fin 30) (Fin K) ℝ) (y : Fin 30 → ℝ) (i : Fin 30) : ℝ :=
  y i - X.mulVec (olsCoefficients X y) i

/-- "v=N/(N-K) sum_i (G_Ti e_i)^2" (targets S7),
HC1 variance of a specified coefficient; the treatment coordinate is 1. -/
def hc1Variance {K : ℕ} (X : Matrix (Fin 30) (Fin K) ℝ) (y : Fin 30 → ℝ) (t : Fin K) : ℝ :=
  (30 : ℝ) / (30 - (K : ℝ)) *
    ∑ i : Fin 30, (olsOperator X t i * olsResidual X y i) ^ 2

/-- "q=beta_hat_T²/v" (targets S7), the squared HC1 statistic. -/
def olsSquaredStatistic {K : ℕ} (X : Matrix (Fin 30) (Fin K) ℝ)
    (y : Fin 30 → ℝ) (t : Fin K) : ℝ := olsCoefficients X y t ^ 2 / hc1Variance X y t

/-- The exact eight q values of Table 1 (T5(iii), targets S7 exact recalculation).
Outcome order is total, bulk, café, book; adjusted is the boolean specification flag. -/
def tableSquaredStatistic (adjusted : Bool) : Fin 4 → ℝ :=
  if adjusted then ![1200277903320876335774 / 280628848000463708694463,
    bulkSquaredStatistic, cafeSquaredStatistic, 3084161273413343448962 / 24391999904970062376441]
  else ![263679812816672 / 522999591200175, 23273498735648 / 15141092298015,
    1492978176032 / 21949506186495, 9067019347232 / 22381571766655]

/-- P040-T5(iii): all eight exact rational q values are positive, no larger
than unadjusted bulk, and that largest value is below 8/5. -/
theorem table_statistics_bounded :
    tableSquaredStatistic false 1 < (8 : ℝ) / 5 ∧
    ∀ a : Bool, ∀ o : Fin 4, 0 < tableSquaredStatistic a o ∧
      tableSquaredStatistic a o ≤ tableSquaredStatistic false 1 := by
  constructor
  · norm_num [tableSquaredStatistic]
  · intro a o
    cases a <;> fin_cases o <;> norm_num [tableSquaredStatistic, cafeSquaredStatistic, bulkSquaredStatistic]

/-- Exact arithmetic witness for "XᵀX" (targets S7),
for the unadjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def unadjustedGramCertificate : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![30, 16],
    ![16, 16]]

/-- Exact arithmetic witness for "(XᵀX)^(-1)" (targets S7),
for the unadjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def unadjustedInverseCertificate : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![(1 / 14), (-1 / 14)],
    ![(-1 / 14), (15 / 112)]]

/-- Exact arithmetic witness for "Xᵀy" (targets S7),
for the unadjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def unadjustedCrossproductCertificate : Fin 4 → Fin 2 → ℝ :=
  ![![(892373 / 50), (979203 / 100)],
    ![(250661 / 100), (14993 / 10)],
    ![(995423 / 100), (263389 / 50)],
    ![(269331 / 50), (60499 / 20)]]

/-- Exact arithmetic witness for "beta_hat=Gy" (targets S7),
for the unadjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def unadjustedCoefficientCertificate : Fin 4 → Fin 2 → ℝ :=
  ![![(805543 / 1400), (410077 / 11200)],
    ![(100731 / 1400), (121831 / 5600)],
    ![(93729 / 280), (-30857 / 5600)],
    ![(236167 / 1400), (228129 / 11200)]]

/-- Exact arithmetic witness for "G_Ti" (targets S7),
for the unadjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def unadjustedTreatmentWeightsCertificate : Fin 30 → ℝ :=
  ![(-1 / 14), (-1 / 14), (1 / 16), (-1 / 14), (1 / 16), (-1 / 14), (1 / 16), (1 / 16), (1 / 16), (1 / 16), (1 / 16), (-1 / 14), (-1 / 14), (-1 / 14), (1 / 16), (-1 / 14), (-1 / 14), (1 / 16), (1 / 16), (-1 / 14), (1 / 16), (1 / 16), (1 / 16), (1 / 16), (-1 / 14), (-1 / 14), (-1 / 14), (1 / 16), (-1 / 14), (1 / 16)]

/-- Exact arithmetic witness for "e=y-X beta_hat" (targets S7),
for the unadjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def unadjustedResidualCertificate : Fin 4 → Fin 30 → ℝ :=
  ![![(117659 / 1400), (2151 / 280), (-88083 / 1600), (-15163 / 56), (-118691 / 1600), (-8447 / 280), (43213 / 1600), (7605 / 64), (370957 / 1600), (-274643 / 1600), (-18131 / 1600), (361791 / 1400), (102301 / 1400), (28087 / 1400), (-2483 / 1600), (268019 / 1400), (-131219 / 1400), (-140099 / 1600), (-137907 / 1600), (-42963 / 1400), (-54931 / 1600), (-195267 / 1600), (625821 / 1600), (-296323 / 1600), (689 / 1400), (-83213 / 1400), (-31749 / 1400), (208893 / 1600), (-178847 / 1400), (-112451 / 1600)],
    ![(17149 / 1400), (12879 / 1400), (203 / 32), (-76861 / 1400), (7203 / 800), (-773 / 280), (711 / 160), (10663 / 160), (63043 / 800), (-2365 / 32), (-30573 / 800), (151703 / 1400), (123717 / 1400), (-19559 / 1400), (-10149 / 800), (-55441 / 1400), (-29583 / 1400), (-2013 / 32), (22923 / 800), (-30899 / 1400), (-13669 / 800), (-8201 / 160), (9279 / 160), (-981 / 32), (67451 / 1400), (-74061 / 1400), (-16857 / 1400), (16331 / 800), (-65773 / 1400), (11531 / 800)],
    ![(82283 / 1400), (45953 / 1400), (-28709 / 800), (-185957 / 1400), (-28821 / 800), (-41603 / 1400), (73379 / 800), (-4217 / 160), (41563 / 800), (-61349 / 800), (-5297 / 160), (26097 / 280), (33731 / 1400), (8853 / 1400), (-9 / 160), (-33357 / 1400), (-124119 / 1400), (-11397 / 800), (-7749 / 800), (38813 / 1400), (47811 / 800), (-1901 / 800), (57003 / 800), (-76989 / 800), (6791 / 280), (-1609 / 280), (3991 / 280), (79363 / 800), (-947 / 1400), (-34589 / 800)],
    ![(18227 / 1400), (-48077 / 1400), (-8163 / 320), (-116257 / 1400), (-15091 / 320), (3233 / 1400), (-22131 / 320), (25133 / 320), (32349 / 320), (-6739 / 320), (19197 / 320), (79603 / 1400), (-55147 / 1400), (38793 / 1400), (3581 / 320), (356817 / 1400), (22483 / 1400), (-3331 / 320), (-33651 / 320), (-50877 / 1400), (-24643 / 320), (-21891 / 320), (16761 / 64), (-18659 / 320), (-100717 / 1400), (-1107 / 1400), (-34847 / 1400), (3501 / 320), (-112127 / 1400), (-13267 / 320)]]

/-- Exact arithmetic witness for "v=N/(N-K) sum_i (G_Ti e_i)^2" (targets S7),
for the unadjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def unadjustedVarianceCertificate : Fin 4 → ℝ :=
  ![(20919983648007 / 7867596800), (3028218459603 / 9834496000), (4389901237299 / 9834496000), (40286829179979 / 39337984000)]

/-- Finite lemma for T4/T5: the unadjusted Gram certificate equals XᵀX,
with entries given by 30-term sums. -/
theorem unadjusted_gram_certificate :
    unadjustedDesign.transpose * unadjustedDesign = unadjustedGramCertificate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [unadjustedDesign, unadjustedGramCertificate, centeredWeekday, recorded_day_summary.1,
      recorded_day_summary.2, salesDay, salesTreatment]

/-- Finite lemma for T4/T5: the proposed unadjusted inverse times the Gram
matrix is the identity. No determinant expansion is used. -/
theorem unadjusted_inverse_product_certificate :
    unadjustedInverseCertificate * unadjustedGramCertificate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [unadjustedInverseCertificate, unadjustedGramCertificate]

/-- Finite lemma for T4/T5: the inverse certificate is the genuine
inverse in the paper’s unadjusted OLS operator. -/
theorem unadjusted_gram_inverse :
    (unadjustedDesign.transpose * unadjustedDesign)⁻¹ = unadjustedInverseCertificate := by
  rw [unadjusted_gram_certificate]
  exact Matrix.inv_eq_left_inv unadjusted_inverse_product_certificate

/-- Finite lemma for T4/T5: the unadjusted Xᵀy certificate for all four
outcomes, computed from the exact recorded CAD values. -/
theorem unadjusted_crossproduct_certificate (o : Fin 4) :
    unadjustedDesign.transpose.mulVec (tableOutcome o) = unadjustedCrossproductCertificate o := by
  ext j
  fin_cases o <;> fin_cases j <;>
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [unadjustedDesign, unadjustedCrossproductCertificate, centeredWeekday, recorded_day_summary.1,
      recorded_day_summary.2, salesDay, salesTreatment, tableOutcome, salesTotal,
      salesBook, salesCafe, salesBulk]

/-- Finite lemma for T4/T5: all unadjusted OLS coefficients, using exact
Gram and crossproduct certificates rather than an assumed fit. -/
theorem unadjusted_coefficients_certificate (o : Fin 4) :
    olsCoefficients unadjustedDesign (tableOutcome o) = unadjustedCoefficientCertificate o := by
  unfold olsCoefficients olsOperator
  rw [unadjusted_gram_inverse, ← Matrix.mulVec_mulVec, unadjusted_crossproduct_certificate]
  ext j
  fin_cases o <;> fin_cases j <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [unadjustedInverseCertificate, unadjustedCrossproductCertificate, unadjustedCoefficientCertificate]

/-- Finite lemma for T4/T5: the treatment row of the unadjusted OLS
operator, the weights used in the HC1 variance. -/
theorem unadjusted_treatment_weights_certificate :
    olsOperator unadjustedDesign 1 = unadjustedTreatmentWeightsCertificate := by
  funext i
  unfold olsOperator
  rw [unadjusted_gram_inverse]
  fin_cases i <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [unadjustedInverseCertificate, unadjustedTreatmentWeightsCertificate, unadjustedDesign,
      centeredWeekday, recorded_day_summary.1, recorded_day_summary.2, salesDay, salesTreatment]

/-- Finite lemma for T4/T5: every residual of the unadjusted regression
is computed from the exact coefficients and recorded outcomes. -/
theorem unadjusted_residuals_certificate (o : Fin 4) (i : Fin 30) :
    olsResidual unadjustedDesign (tableOutcome o) i = unadjustedResidualCertificate o i := by
  unfold olsResidual
  rw [unadjusted_coefficients_certificate]
  fin_cases o <;> fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [unadjustedCoefficientCertificate, unadjustedResidualCertificate, unadjustedDesign, centeredWeekday,
      recorded_day_summary.1, recorded_day_summary.2, salesDay, salesTreatment,
      tableOutcome, salesTotal, salesBook, salesCafe, salesBulk]

/-- Finite lemma for T4/T5: the exact unadjusted HC1 treatment variance
for each outcome, expressed as a 30-term sum of squares. -/
theorem unadjusted_hc1_variance_certificate (o : Fin 4) :
    hc1Variance unadjustedDesign (tableOutcome o) 1 = unadjustedVarianceCertificate o := by
  unfold hc1Variance
  simp_rw [unadjusted_treatment_weights_certificate, unadjusted_residuals_certificate]
  fin_cases o <;> simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [unadjustedTreatmentWeightsCertificate, unadjustedResidualCertificate, unadjustedVarianceCertificate]

/-- T4/T5: each unadjusted exact squared statistic is identified with
the actual OLS/HC1 calculation, not merely supplied as a witness. -/
theorem unadjusted_squared_statistics_certificate (o : Fin 4) :
    olsSquaredStatistic unadjustedDesign (tableOutcome o) 1 = tableSquaredStatistic false o := by
  unfold olsSquaredStatistic
  rw [unadjusted_coefficients_certificate, unadjusted_hc1_variance_certificate]
  fin_cases o <;> norm_num [unadjustedCoefficientCertificate, unadjustedVarianceCertificate,
    tableSquaredStatistic, cafeSquaredStatistic, bulkSquaredStatistic]

/-- Exact arithmetic witness for "XᵀX" (targets S7),
for the adjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def adjustedGramCertificate : Matrix (Fin 9) (Fin 9) ℝ :=
  ![![30, 16, 0, 0, 0, 0, 0, 0, 0],
    ![16, 16, (92 / 15), (-32 / 15), (1 / 3), (1 / 3), (4 / 3), (-2 / 15), (2 / 5)],
    ![0, (92 / 15), (70649 / 30), (68 / 15), (-41 / 6), (-11 / 6), (19 / 6), (-112 / 15), (79 / 10)],
    ![0, (-32 / 15), (68 / 15), (52 / 15), (-2 / 3), (-2 / 3), (-2 / 3), (-8 / 15), (-2 / 5)],
    ![0, (1 / 3), (-41 / 6), (-2 / 3), (25 / 6), (-5 / 6), (-5 / 6), (-2 / 3), (-1 / 2)],
    ![0, (1 / 3), (-11 / 6), (-2 / 3), (-5 / 6), (25 / 6), (-5 / 6), (-2 / 3), (-1 / 2)],
    ![0, (4 / 3), (19 / 6), (-2 / 3), (-5 / 6), (-5 / 6), (25 / 6), (-2 / 3), (-1 / 2)],
    ![0, (-2 / 15), (-112 / 15), (-8 / 15), (-2 / 3), (-2 / 3), (-2 / 3), (52 / 15), (-2 / 5)],
    ![0, (2 / 5), (79 / 10), (-2 / 5), (-1 / 2), (-1 / 2), (-1 / 2), (-2 / 5), (27 / 10)]]

/-- Exact arithmetic witness for "(XᵀX)^(-1)" (targets S7),
for the adjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def adjustedInverseCertificate : Matrix (Fin 9) (Fin 9) ℝ :=
  ![![(3379 / 41210), (-376 / 4121), (8 / 28847), (-1324 / 28847), (1376 / 144235), (1336 / 144235), (3928 / 144235), (16 / 28847), (1256 / 86541)],
    ![(-376 / 4121), (705 / 4121), (-15 / 28847), (4965 / 57694), (-516 / 28847), (-501 / 28847), (-1473 / 28847), (-30 / 28847), (-785 / 28847)],
    ![(8 / 28847), (-15 / 28847), (88 / 201929), (-281 / 403858), (285 / 403858), (109 / 403858), (-25 / 403858), (176 / 201929), (-405 / 403858)],
    ![(-1324 / 28847), (4965 / 57694), (-281 / 403858), (439175 / 807716), (194135 / 807716), (194697 / 807716), (181357 / 807716), (200805 / 807716), (191749 / 807716)],
    ![(1376 / 144235), (-516 / 28847), (285 / 403858), (194135 / 807716), (91443 / 201929), (509147 / 2019290), (257473 / 1009645), (203069 / 807716), (50728 / 201929)],
    ![(1336 / 144235), (-501 / 28847), (109 / 403858), (194697 / 807716), (509147 / 2019290), (91246 / 201929), (515071 / 2019290), (202365 / 807716), (101861 / 403858)],
    ![(3928 / 144235), (-1473 / 28847), (-25 / 403858), (181357 / 807716), (257473 / 1009645), (515071 / 2019290), (469838 / 1009645), (201829 / 807716), (52232 / 201929)],
    ![(16 / 28847), (-30 / 28847), (176 / 201929), (200805 / 807716), (203069 / 807716), (202365 / 807716), (201829 / 807716), (202633 / 403858), (200309 / 807716)],
    ![(1256 / 86541), (-785 / 28847), (-405 / 403858), (191749 / 807716), (50728 / 201929), (101861 / 403858), (52232 / 201929), (200309 / 807716), (119214 / 201929)]]

/-- Exact arithmetic witness for "Xᵀy" (targets S7),
for the adjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def adjustedCrossproductCertificate : Fin 4 → Fin 9 → ℝ :=
  ![![(892373 / 50), (979203 / 100), (-1595413 / 1500), (-132857 / 1500), (71863 / 300), (-8447 / 75), (110687 / 150), (-1089347 / 1500), (-20939 / 250)],
    ![(250661 / 100), (14993 / 10), (-4705831 / 3000), (1907 / 375), (7981 / 600), (-16697 / 600), (88177 / 600), (-137621 / 750), (-44241 / 1000)],
    ![(995423 / 100), (263389 / 50), (4553357 / 3000), (18041 / 375), (188371 / 600), (913 / 600), (7747 / 600), (-295253 / 750), (-25303 / 1000)],
    ![(269331 / 50), (60499 / 20), (-126598 / 125), (-70883 / 500), (-8771 / 100), (-2158 / 25), (14451 / 25), (-74533 / 500), (-3553 / 250)]]

/-- Exact arithmetic witness for "beta_hat=Gy" (targets S7),
for the adjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def adjustedCoefficientCertificate : Fin 4 → Fin 9 → ℝ :=
  ![![(1222827243 / 2060500), (2246851 / 824200), (-576977 / 576940), (-325531313 / 11538800), (543820671 / 14423500), (-457659703 / 14423500), (4004906963 / 28847000), (-553833923 / 2884700), (-197919399 / 5769400)],
    ![(880142141 / 12363000), (955199 / 41210), (-147431 / 164840), (-14503783 / 1648400), (-48530883 / 2060500), (-127275337 / 4121000), (171047 / 515125), (-115744511 / 1648400), (-4010557 / 103025)],
    ![(1386920861 / 4121000), (-146561 / 16484), (91121 / 164840), (-5919137 / 1648400), (222075693 / 4121000), (-18853569 / 2060500), (-930779 / 164840), (-35582999 / 329680), (-3124423 / 164840)],
    ![(1148029367 / 6181500), (-9529079 / 824200), (-94973 / 144235), (-182570873 / 11538800), (212543853 / 28847000), (239557919 / 28847000), (519776832 / 3605875), (-3194383 / 230776), (68013299 / 2884700)]]

/-- Exact arithmetic witness for "G_Ti" (targets S7),
for the adjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def adjustedTreatmentWeightsCertificate : Fin 30 → ℝ :=
  ![(-393 / 4121), (-393 / 4121), (171 / 4121), (-330 / 4121), (375 / 4121), (45 / 8242), (297 / 4121), (297 / 4121), (12 / 317), (360 / 4121), (250 / 4121), (-345 / 4121), (15 / 8242), (-423 / 4121), (282 / 4121), (-564 / 4121), (-360 / 4121), (235 / 4121), (345 / 4121), (-15 / 8242), (267 / 4121), (267 / 4121), (126 / 4121), (330 / 4121), (-485 / 4121), (-375 / 4121), (-45 / 8242), (252 / 4121), (-453 / 4121), (111 / 4121)]

/-- Exact arithmetic witness for "e=y-X beta_hat" (targets S7),
for the adjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def adjustedResidualCertificate : Fin 4 → Fin 30 → ℝ :=
  ![![(17476179 / 4121000), (-6944867 / 4121000), (-824587859 / 4121000), (-97152677 / 824200), (-31892923 / 412100), (-62726851 / 1648400), (-24530023 / 2060500), (77448586 / 515125), (29736607 / 317000), (4559727 / 206050), (21234841 / 824200), (188185733 / 824200), (23798701 / 329680), (-188487701 / 4121000), (76175779 / 2060500), (13657447 / 515125), (60303231 / 824200), (-7164831 / 164840), (-15536237 / 206050), (-40504939 / 1648400), (-122072243 / 2060500), (-157669441 / 2060500), (1100707681 / 4121000), (9305269 / 412100), (7294657 / 412100), (-62254939 / 824200), (-3152343 / 329680), (232108027 / 2060500), (-449656497 / 4121000), (-771955289 / 4121000)],
    ![(-647151 / 1030250), (4685423 / 1030250), (-61924623 / 2060500), (-30382767 / 1648400), (-20092337 / 824200), (-41252989 / 1648400), (-14820129 / 4121000), (275405417 / 4121000), (15427603 / 317000), (-53737457 / 1648400), (-900147 / 32968), (8516206 / 103025), (119285873 / 1648400), (-29520187 / 2060500), (-3214136 / 515125), (-63930049 / 1030250), (45924041 / 1648400), (-4711636 / 103025), (6423363 / 824200), (-52443253 / 1648400), (-51944409 / 4121000), (-158859633 / 4121000), (166401679 / 4121000), (38196183 / 1648400), (60196763 / 824200), (-27230337 / 412100), (-25589631 / 1648400), (32098379 / 1030250), (-27393597 / 1030250), (3152231 / 1030250)],
    ![(2732881 / 2060500), (78015309 / 2060500), (-3247636 / 103025), (-49635493 / 1648400), (-16058593 / 412100), (-54398457 / 1648400), (139240077 / 4121000), (-89862797 / 4121000), (665037 / 12680), (42100629 / 1648400), (-16822037 / 824200), (68418237 / 824200), (27923477 / 1648400), (-121286519 / 2060500), (321666 / 515125), (-12603207 / 412100), (2083479 / 329680), (-223343 / 41210), (-4196557 / 206050), (27528699 / 1648400), (-24359433 / 4121000), (-22933567 / 4121000), (10551199 / 164840), (-2882531 / 1648400), (21288897 / 824200), (-19514823 / 824200), (-1053719 / 1648400), (15278329 / 515125), (-22903791 / 2060500), (-22397949 / 412100)],
    ![(14599021 / 4121000), (-181717177 / 4121000), (-570833173 / 4121000), (-57143547 / 824200), (-11576323 / 824200), (6584919 / 329680), (-86739997 / 2060500), (108511517 / 1030250), (-2316921 / 317000), (12028661 / 412100), (60560553 / 824200), (6454731 / 103025), (-5643169 / 329680), (113125711 / 4121000), (87745659 / 2060500), (245505921 / 2060500), (32132513 / 824200), (6335793 / 824200), (-51782083 / 824200), (-3118077 / 329680), (-41960161 / 1030250), (-66772841 / 2060500), (670526027 / 4121000), (119214 / 103025), (-33448173 / 412100), (5860279 / 412100), (2176327 / 329680), (106797953 / 2060500), (-294274527 / 4121000), (-560584723 / 4121000)]]

/-- Exact arithmetic witness for "v=N/(N-K) sum_i (G_Ti e_i)^2" (targets S7),
for the adjusted recorded design. Its identification is proved below;
this internal certificate is not an additional modelling assumption. -/
def adjustedVarianceCertificate : Fin 4 → ℝ :=
  ![(280628848000463708694463 / 161509653387533360000), (10415886991743115636339 / 23072807626790480000), (42131842162249950707521 / 161509653387533360000), (24391999904970062376441 / 23072807626790480000)]

/-- Finite lemma for T4/T5: the adjusted Gram certificate equals XᵀX,
with entries given by 30-term sums. -/
theorem adjusted_gram_certificate :
    adjustedDesign.transpose * adjustedDesign = adjustedGramCertificate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [adjustedDesign, adjustedGramCertificate, centeredWeekday, recorded_day_summary.1,
      recorded_day_summary.2, salesDay, salesTreatment]

/-- Finite lemma for T4/T5: the proposed adjusted inverse times the Gram
matrix is the identity. No determinant expansion is used. -/
theorem adjusted_inverse_product_certificate :
    adjustedInverseCertificate * adjustedGramCertificate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [adjustedInverseCertificate, adjustedGramCertificate]

/-- Finite lemma for T4/T5: the inverse certificate is the genuine
inverse in the paper’s adjusted OLS operator. -/
theorem adjusted_gram_inverse :
    (adjustedDesign.transpose * adjustedDesign)⁻¹ = adjustedInverseCertificate := by
  rw [adjusted_gram_certificate]
  exact Matrix.inv_eq_left_inv adjusted_inverse_product_certificate

/-- Finite lemma for T4/T5: the adjusted Xᵀy certificate for all four
outcomes, computed from the exact recorded CAD values. -/
theorem adjusted_crossproduct_certificate (o : Fin 4) :
    adjustedDesign.transpose.mulVec (tableOutcome o) = adjustedCrossproductCertificate o := by
  ext j
  fin_cases o <;> fin_cases j <;>
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [adjustedDesign, adjustedCrossproductCertificate, centeredWeekday, recorded_day_summary.1,
      recorded_day_summary.2, salesDay, salesTreatment, tableOutcome, salesTotal,
      salesBook, salesCafe, salesBulk]

/-- Finite lemma for T4/T5: all adjusted OLS coefficients, using exact
Gram and crossproduct certificates rather than an assumed fit. -/
theorem adjusted_coefficients_certificate (o : Fin 4) :
    olsCoefficients adjustedDesign (tableOutcome o) = adjustedCoefficientCertificate o := by
  unfold olsCoefficients olsOperator
  rw [adjusted_gram_inverse, ← Matrix.mulVec_mulVec, adjusted_crossproduct_certificate]
  ext j
  fin_cases o <;> fin_cases j <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [adjustedInverseCertificate, adjustedCrossproductCertificate, adjustedCoefficientCertificate]

/-- Finite lemma for T4/T5: the treatment row of the adjusted OLS
operator, the weights used in the HC1 variance. -/
theorem adjusted_treatment_weights_certificate :
    olsOperator adjustedDesign 1 = adjustedTreatmentWeightsCertificate := by
  funext i
  unfold olsOperator
  rw [adjusted_gram_inverse]
  fin_cases i <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [adjustedInverseCertificate, adjustedTreatmentWeightsCertificate, adjustedDesign,
      centeredWeekday, recorded_day_summary.1, recorded_day_summary.2, salesDay, salesTreatment]

/-- Finite lemma for T4/T5: every residual of the adjusted regression
is computed from the exact coefficients and recorded outcomes. -/
theorem adjusted_residuals_certificate (o : Fin 4) (i : Fin 30) :
    olsResidual adjustedDesign (tableOutcome o) i = adjustedResidualCertificate o i := by
  unfold olsResidual
  rw [adjusted_coefficients_certificate]
  fin_cases o <;> fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [adjustedCoefficientCertificate, adjustedResidualCertificate, adjustedDesign, centeredWeekday,
      recorded_day_summary.1, recorded_day_summary.2, salesDay, salesTreatment,
      tableOutcome, salesTotal, salesBook, salesCafe, salesBulk]

/-- Finite lemma for T4/T5: the exact adjusted HC1 treatment variance
for each outcome, expressed as a 30-term sum of squares. -/
theorem adjusted_hc1_variance_certificate (o : Fin 4) :
    hc1Variance adjustedDesign (tableOutcome o) 1 = adjustedVarianceCertificate o := by
  unfold hc1Variance
  simp_rw [adjusted_treatment_weights_certificate, adjusted_residuals_certificate]
  fin_cases o <;> simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [adjustedTreatmentWeightsCertificate, adjustedResidualCertificate, adjustedVarianceCertificate]

/-- T4/T5: each adjusted exact squared statistic is identified with
the actual OLS/HC1 calculation, not merely supplied as a witness. -/
theorem adjusted_squared_statistics_certificate (o : Fin 4) :
    olsSquaredStatistic adjustedDesign (tableOutcome o) 1 = tableSquaredStatistic true o := by
  unfold olsSquaredStatistic
  rw [adjusted_coefficients_certificate, adjusted_hc1_variance_certificate]
  fin_cases o <;> norm_num [adjustedCoefficientCertificate, adjustedVarianceCertificate,
    tableSquaredStatistic, cafeSquaredStatistic, bulkSquaredStatistic]

/-- P040-T4 B1–B2 and T5(iii): the OLS/HC1 calculation on the 30 recorded
rows yields the stated café/bulk coefficients, variances and all eight exact q
values, as established by the separate small arithmetic certificates. -/
theorem recorded_regression_identification :
    olsCoefficients adjustedDesign salesCafe 1 = cafeCoefficientWitness ∧
    hc1Variance adjustedDesign salesCafe 1 = cafeVarianceWitness ∧
    olsCoefficients adjustedDesign salesBulk 1 = bulkCoefficientWitness ∧
    hc1Variance adjustedDesign salesBulk 1 = bulkVarianceWitness ∧
    (∀ o : Fin 4, olsSquaredStatistic unadjustedDesign (tableOutcome o) 1 = tableSquaredStatistic false o) ∧
    (∀ o : Fin 4, olsSquaredStatistic adjustedDesign (tableOutcome o) 1 = tableSquaredStatistic true o) := by
  have hca := congrFun (adjusted_coefficients_certificate (2 : Fin 4)) (1 : Fin 9)
  have hcv := adjusted_hc1_variance_certificate (2 : Fin 4)
  have hba := congrFun (adjusted_coefficients_certificate (1 : Fin 4)) (1 : Fin 9)
  have hbv := adjusted_hc1_variance_certificate (1 : Fin 4)
  norm_num [tableOutcome, adjustedCoefficientCertificate, adjustedVarianceCertificate,
    cafeCoefficientWitness, cafeVarianceWitness, bulkCoefficientWitness, bulkVarianceWitness] at hca hcv hba hbv
  exact ⟨by norm_num [cafeCoefficientWitness]; exact hca,
    by norm_num [cafeVarianceWitness]; exact hcv,
    by norm_num [bulkCoefficientWitness]; exact hba,
    by norm_num [bulkVarianceWitness]; exact hbv, unadjusted_squared_statistics_certificate,
    adjusted_squared_statistics_certificate⟩

/-- Normal tail p values decrease as the nonnegative squared statistic
increases (T5(iii), finite analytic lemma). -/
theorem normal_reference_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    normalReferenceP b ≤ normalReferenceP a := by
  have hf : Continuous (fun t : ℝ => Real.exp (-t ^ 2 / 2)) := by fun_prop
  have hi := intervalIntegral.integral_mono_interval (μ := volume)
    (a := 0) (b := Real.sqrt a) (c := 0) (d := Real.sqrt b)
    le_rfl (Real.sqrt_nonneg a) (Real.sqrt_le_sqrt hab)
    (Filter.Eventually.of_forall (fun t => Real.exp_nonneg _)) (hf.intervalIntegrable _ _)
  have hh := mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg (2 / Real.pi))
  unfold normalReferenceP
  linarith

/-- For any positive reference degrees of freedom, the Student-t density is
continuous and nonnegative (T5(iii)); no null-distribution claim is made. -/
theorem student_density_regular {nu : ℝ} (hnu : 0 < nu) :
    Continuous (studentReferenceDensity nu) ∧ ∀ t, 0 ≤ studentReferenceDensity nu t := by
  have hb : Continuous (fun t : ℝ => 1 + t ^ 2 / nu) := by fun_prop
  have hbase (t : ℝ) : 0 < 1 + t ^ 2 / nu := by positivity
  constructor
  · unfold studentReferenceDensity
    exact continuous_const.mul (hb.rpow_const (fun t => Or.inl (hbase t).ne'))
  · intro t
    unfold studentReferenceDensity
    have hg1 := Real.Gamma_pos_of_pos (show 0 < (nu + 1) / 2 by linarith)
    have hg2 := Real.Gamma_pos_of_pos (show 0 < nu / 2 by linarith)
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (hbase t).le _)

/-- Student-t reference p values decrease with the nonnegative squared
statistic, at any fixed positive ν (T5(iii)). -/
theorem student_reference_antitone {a b nu : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hnu : 0 < nu) :
    studentReferenceP b nu ≤ studentReferenceP a nu := by
  have hf := student_density_regular hnu
  have hi := intervalIntegral.integral_mono_interval (μ := volume)
    (a := 0) (b := Real.sqrt a) (c := 0) (d := Real.sqrt b)
    le_rfl (Real.sqrt_nonneg a) (Real.sqrt_le_sqrt hab)
    (Filter.Eventually.of_forall hf.2) (hf.1.intervalIntegrable _ _)
  unfold studentReferenceP
  linarith

/-- At the upper bound q=8/5 for all eight statistics, the normal and
Student-t(21) reference p values remain above .10 (T5(iii)). -/
theorem reference_p_at_max_21 :
    (1 : ℝ) / 10 < normalReferenceP (8 / 5) ∧
    (1 : ℝ) / 10 < studentReferenceP (8 / 5) 21 := by
  have hn := normal_decimal_certificate (q := 8 / 5)
    (alo := 10092529 / 10000000) (ahi := 10092532 / 10000000)
    (plo := 20 / 100) (phi := 21 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num [normalIntegratedSeries, Finset.sum_range_succ, normalTaylorError, Nat.factorial])
    (by norm_num [normalIntegratedSeries, Finset.sum_range_succ, normalTaylorError, Nat.factorial])
    (by norm_num [normalIntegratedSeries, Finset.sum_range_succ, normalTaylorError, Nat.factorial])
  have ht := student21_decimal_certificate (q := 8 / 5)
    (alo := 9973136 / 10000000) (ahi := 9973141 / 10000000)
    (plo := 21 / 100) (phi := 23 / 100)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [student21Scale, Nat.choose]) (by norm_num [student21Scale, Nat.choose])
    (by norm_num [student21IntegratedSeries, Finset.sum_range_succ, Nat.choose])
    (by norm_num [student21IntegratedSeries, Finset.sum_range_succ, Nat.choose])
    (by norm_num [student21IntegratedSeries, Finset.sum_range_succ, Nat.choose])
    (by norm_num [student21IntegratedSeries, Finset.sum_range_succ, Nat.choose])
  constructor <;> linarith [hn.1, ht.1]

/-- Twice the Student-t(28) density's constant, after removing sqrt(28),
from Gamma(29/2)/(sqrt(28 pi) Gamma(14)) (targets S7, T5(iii)). -/
def student28Scale : ℝ := (2 * 213458046676875 : ℝ) / (16384 * 6227020800)

/-- The actual Student-t(28) density has its explicit Gamma normalization
(T5(iii)); the half-integer power is retained, not replaced in the definition. -/
theorem student28_density_identity (t : ℝ) :
    studentReferenceDensity 28 t = student28Scale / (2 * Real.sqrt 28) *
      (1 + t ^ 2 / 28) ^ (-(29 / 2 : ℝ)) := by
  have hg14 : Real.Gamma 14 = (6227020800 : ℝ) := by
    convert Real.Gamma_nat_eq_factorial 13 using 1 <;> norm_num [Nat.factorial]
  have hghalf : Real.Gamma (29 / 2) = (213458046676875 : ℝ) * Real.sqrt Real.pi / 16384 := by
    convert Real.Gamma_nat_add_half 14 using 1 <;> norm_num [Nat.doubleFactorial]
  have hs28 : Real.sqrt (28 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hspi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold studentReferenceDensity student28Scale
  norm_num [hg14, hghalf]
  field_simp [hs28, hspi]
  norm_num

/-- A polynomial upper bound on the Student-t(28) kernel (T5(iii)). The
bound uses exponent -14 solely within a proved inequality; the reference
distribution in studentReferenceP still has the correct exponent -29/2. -/
theorem student28_kernel_upper {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ (-(29 / 2 : ℝ)) ≤ 1 - 14 * x + 105 * x ^ 2 := by
  have hh : (1 + x) ^ (-(29 / 2 : ℝ)) ≤ 1 / (1 + x) ^ 14 := by
    convert Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 1 + x by linarith)
      (by norm_num : -(29 / 2 : ℝ) ≤ -(14 : ℝ)) using 1 <;>
      norm_num [Real.rpow_neg, Real.rpow_natCast, one_div]
  have hp : 1 / (1 + x) ^ 14 ≤ 1 - 14 * x + 105 * x ^ 2 := by
    apply (div_le_iff₀ (pow_pos (show 0 < 1 + x by linarith) 14)).mpr
    have he : (1 - 14 * x + 105 * x ^ 2) * (1 + x) ^ 14 - 1 =
      x ^ 3 * (560 + 5460 * x + 26208 * x ^ 2 + 80080 * x ^ 3 + 171600 * x ^ 4 +
        270270 * x ^ 5 + 320320 * x ^ 6 + 288288 * x ^ 7 + 196560 * x ^ 8 +
        100100 * x ^ 9 + 36960 * x ^ 10 + 9360 * x ^ 11 + 1456 * x ^ 12 + 105 * x ^ 13) := by ring
    have hn : 0 ≤ x ^ 3 * (560 + 5460 * x + 26208 * x ^ 2 + 80080 * x ^ 3 + 171600 * x ^ 4 +
        270270 * x ^ 5 + 320320 * x ^ 6 + 288288 * x ^ 7 + 196560 * x ^ 8 +
        100100 * x ^ 9 + 36960 * x ^ 10 + 9360 * x ^ 11 + 1456 * x ^ 12 + 105 * x ^ 13) := by positivity
    linarith
  exact hh.trans hp

/-- Integral of the coarse polynomial kernel bound for Student-t(28)
(T5(iii)); the expression is exact for each q≥0. -/
theorem student28_polynomial_integral {q : ℝ} (hq : 0 ≤ q) :
    (∫ t in (0 : ℝ)..Real.sqrt q, 1 - 14 * (t ^ 2 / 28) + 105 * (t ^ 2 / 28) ^ 2) =
      Real.sqrt q * (1 - q / 6 + 3 * q ^ 2 / 112) := by
  have he : (fun t : ℝ => 1 - 14 * (t ^ 2 / 28) + 105 * (t ^ 2 / 28) ^ 2) =
      (fun t : ℝ => 1 - (1 / 2 : ℝ) * t ^ 2 + (15 / 112 : ℝ) * t ^ 4) := by
    funext t; ring
  rw [he, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  · simp only [sub_zero, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_pow (by norm_num : (5 : ℕ) ≠ 0), smul_eq_mul]
    have hs := Real.sq_sqrt hq
    rw [show Real.sqrt q ^ 3 = Real.sqrt q * (Real.sqrt q ^ 2) by ring,
      show Real.sqrt q ^ 5 = Real.sqrt q * (Real.sqrt q ^ 2) ^ 2 by ring, hs]
    ring
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _

/-- P040-T5(iii): the Student-t reference with 28 residual degrees of freedom
also gives p>.10 at q=8/5, using a coarse but rigorous density enclosure. -/
theorem reference_p_at_max_28 : (1 : ℝ) / 10 < studentReferenceP (8 / 5) 28 := by
  let q : ℝ := 8 / 5
  let C := student28Scale / (2 * Real.sqrt 28)
  have hC : 0 ≤ C := by dsimp [C, student28Scale]; positivity
  have hf := (student_density_regular (by norm_num : (0 : ℝ) < 28)).1
  have hg : Continuous (fun t : ℝ => C * (1 - 14 * (t ^ 2 / 28) + 105 * (t ^ 2 / 28) ^ 2)) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (Real.sqrt_nonneg q)
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    (fun t ht => by rw [student28_density_identity]; exact
      mul_le_mul_of_nonneg_left (student28_kernel_upper (by positivity)) hC)
  rw [intervalIntegral.integral_const_mul, student28_polynomial_integral (by dsimp [q]; norm_num)] at hi
  let B := student28Scale * Real.sqrt (q / 28)
  have hm : (2 * C) * Real.sqrt q = B := by
    dsimp [C, B]
    rw [Real.sqrt_div (by dsimp [q]; norm_num : 0 ≤ q)]
    ring
  have hB0 : 0 ≤ B := by dsimp [B, student28Scale]; positivity
  have hBsq : B ^ 2 = student28Scale ^ 2 * (q / 28) := by
    dsimp [B]
    rw [mul_pow, Real.sq_sqrt (by dsimp [q]; norm_num : 0 ≤ q / 28)]
  have hBhi : B < (11 : ℝ) / 10 := by
    have hs : B ^ 2 < ((11 : ℝ) / 10) ^ 2 := by
      rw [hBsq]; norm_num [student28Scale, q]
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
  rw [← mul_assoc (2 : ℝ) C (Real.sqrt q * (1 - q / 6 + 3 * q ^ 2 / 112)),
    ← mul_assoc (2 * C) (Real.sqrt q) (1 - q / 6 + 3 * q ^ 2 / 112), hm] at hh
  change (1 : ℝ) / 10 < 1 - 2 * (∫ t in (0 : ℝ)..Real.sqrt q, studentReferenceDensity 28 t)
  have hpolypos : 0 ≤ 1 - q / 6 + 3 * q ^ 2 / 112 := by dsimp [q]; norm_num
  have hb := mul_le_mul_of_nonneg_right hBhi.le hpolypos
  norm_num [q] at hh hb
  linarith

/-- P040-T5(iii): all eight exact statistics yield two-tailed p>.10 under
their own residual degrees of freedom (28 unadjusted, 21 adjusted), and under
the normal reference. This does not assert exact test size under a null law. -/
theorem table_effects_not_significant (a : Bool) (o : Fin 4) :
    (1 : ℝ) / 10 < studentReferenceP (tableSquaredStatistic a o) (if a then 21 else 28) ∧
    (1 : ℝ) / 10 < normalReferenceP (tableSquaredStatistic a o) := by
  have hq0 := (table_statistics_bounded.2 a o).1.le
  have hqmax := (table_statistics_bounded.2 a o).2.trans table_statistics_bounded.1.le
  have hn := normal_reference_antitone hq0 hqmax
  constructor
  · cases a
    · exact reference_p_at_max_28.trans_le (student_reference_antitone hq0 hqmax (by norm_num))
    · exact reference_p_at_max_21.2.trans_le (student_reference_antitone hq0 hqmax (by norm_num))
  · exact reference_p_at_max_21.1.trans_le hn


/-- Auxiliary Taylor coefficients for (1+x)^(-29/2), the Student-t(28) kernel
(targets S7, T5(iii)). The polynomial bounds below are proved by squaring and
finite identities; these coefficients do not substitute a new density. -/
def student28TaylorCoefficient : Fin 12 → ℝ :=
  ![1, (-29 / 2), (899 / 8), (-9889 / 16), (346115 / 128), (-2561251 / 256), (33296263 / 1024), (-195020969 / 2048), (8385901667 / 32768), (-41929508335 / 65536), (394137378349 / 262144), (-1755702867191 / 524288)]

/-- Finite auxiliary polynomial through degree n for the t(28) density kernel
(T5(iii)); its relation to the actual kernel is proved below. -/
def student28Taylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k : Fin 12, if k.val ≤ n then student28TaylorCoefficient k * x ^ k.val else 0

/-- Integrated coefficients of the finite polynomial certificate for t(28)
(T5(iii)); all values used for the decimal checks are rational finite sums. -/
def student28IntegratedSeries (n : ℕ) (q : ℝ) : ℝ :=
  ∑ k : Fin 12, if k.val ≤ n then
    student28TaylorCoefficient k * (q / 28) ^ k.val / (2 * k.val + 1 : ℕ) else 0


/-- Finite square certificate for the degree-10 polynomial bounding the
actual t(28) kernel (T5(iii)), with a positive Horner remainder on [0,.06]. -/
theorem student28_square_certificate_10 {x : ℝ} (hx : 0 ≤ x) (hxu : x ≤ (3 : ℝ) / 50) :
    0 ≤ (1+x)^29 * student28Taylor 10 x ^ 2 - 1 := by
  let H38 : ℝ := (155344273011822773965801 / 68719476736)
  let H37 : ℝ := (4372776025417904892696909 / 68719476736) + x * H38
  let H36 : ℝ := (29658379236226877392783527 / 34359738368) + x * H37
  let H35 : ℝ := (258129375453932912851836915 / 34359738368) + x * H36
  let H34 : ℝ := (3238181610768325325317388175 / 68719476736) + x * H35
  let H33 : ℝ := (15587293630562463745696715955 / 68719476736) + x * H34
  let H32 : ℝ := (14967251271684309847212868905 / 17179869184) + x * H33
  let H31 : ℝ := (47085991679408293422906130035 / 17179869184) + x * H32
  let H30 : ℝ := (494322457491160415398838822265 / 68719476736) + x * H31
  let H29 : ℝ := (1096865616264412628102337994125 / 68719476736) + x * H30
  let H28 : ℝ := (1038881666003184189295250584905 / 34359738368) + x * H29
  let H27 : ℝ := (1691831816412658376468228661445 / 34359738368) + x * H28
  let H26 : ℝ := (4760515745926218039704368553127 / 68719476736) + x * H27
  let H25 : ℝ := (5804353176841532981321883608379 / 68719476736) + x * H26
  let H24 : ℝ := (191960795758612309051793014845 / 2147483648) + x * H25
  let H23 : ℝ := (705383967802599667627966765845 / 8589934592) + x * H24
  let H22 : ℝ := (4493744446333644603192568919715 / 68719476736) + x * H23
  let H21 : ℝ := (3092827225633815757330936868175 / 68719476736) + x * H22
  let H20 : ℝ := (915531968958798455993178434985 / 34359738368) + x * H21
  let H19 : ℝ := (463071706936827439189333479885 / 34359738368) + x * H20
  let H18 : ℝ := (396407978935978026727735030005 / 68719476736) + x * H19
  let H17 : ℝ := (141710219716635654189040480545 / 68719476736) + x * H18
  let H16 : ℝ := (10386960418361481105924858085 / 17179869184) + x * H17
  let H15 : ℝ := (2433642285701873657084816835 / 17179869184) + x * H16
  let H14 : ℝ := (1753372736041694954871295611 / 68719476736) + x * H15
  let H13 : ℝ := (228049802610181623903382551 / 68719476736) + x * H14
  let H12 : ℝ := (9536465342240896850557767 / 34359738368) + x * H13
  let H11 : ℝ := (385331599068766703831387 / 34359738368) + x * H12
  let H10 : ℝ := (131893858365231407445 / 68719476736) + x * H11
  let H9 : ℝ := (307752336185539950705 / 68719476736) + x * H10
  let H8 : ℝ := (66262464728944008525 / 8589934592) + x * H9
  let H7 : ℝ := (10760571195298599675 / 1073741824) + x * H8
  let H6 : ℝ := (2658494060014948155 / 268435456) + x * H7
  let H5 : ℝ := (7975482180044844465 / 1073741824) + x * H6
  let H4 : ℝ := (139920740000786745 / 33554432) + x * H5
  let H3 : ℝ := (14277626530692525 / 8388608) + x * H4
  let H2 : ℝ := (1002776445299475 / 2097152) + x * H3
  let H1 : ℝ := (173814583851909 / 2097152) + x * H2
  let H0 : ℝ := (1755702867191 / 262144) + x * H1
  have hH38 : (155344273011822773965801 / 68719476736) ≤ H38 := by dsimp [H38]; norm_num
  have hH37 : (4372776025417904892696909 / 68719476736) ≤ H37 := by
    change (4372776025417904892696909 / 68719476736) ≤ (4372776025417904892696909 / 68719476736) + x * H38
    have hn : 0 ≤ H38 := (by norm_num : (0 : ℝ) ≤ (155344273011822773965801 / 68719476736)).trans hH38
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH36 : (29658379236226877392783527 / 34359738368) ≤ H36 := by
    change (29658379236226877392783527 / 34359738368) ≤ (29658379236226877392783527 / 34359738368) + x * H37
    have hn : 0 ≤ H37 := (by norm_num : (0 : ℝ) ≤ (4372776025417904892696909 / 68719476736)).trans hH37
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH35 : (258129375453932912851836915 / 34359738368) ≤ H35 := by
    change (258129375453932912851836915 / 34359738368) ≤ (258129375453932912851836915 / 34359738368) + x * H36
    have hn : 0 ≤ H36 := (by norm_num : (0 : ℝ) ≤ (29658379236226877392783527 / 34359738368)).trans hH36
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH34 : (3238181610768325325317388175 / 68719476736) ≤ H34 := by
    change (3238181610768325325317388175 / 68719476736) ≤ (3238181610768325325317388175 / 68719476736) + x * H35
    have hn : 0 ≤ H35 := (by norm_num : (0 : ℝ) ≤ (258129375453932912851836915 / 34359738368)).trans hH35
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH33 : (15587293630562463745696715955 / 68719476736) ≤ H33 := by
    change (15587293630562463745696715955 / 68719476736) ≤ (15587293630562463745696715955 / 68719476736) + x * H34
    have hn : 0 ≤ H34 := (by norm_num : (0 : ℝ) ≤ (3238181610768325325317388175 / 68719476736)).trans hH34
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH32 : (14967251271684309847212868905 / 17179869184) ≤ H32 := by
    change (14967251271684309847212868905 / 17179869184) ≤ (14967251271684309847212868905 / 17179869184) + x * H33
    have hn : 0 ≤ H33 := (by norm_num : (0 : ℝ) ≤ (15587293630562463745696715955 / 68719476736)).trans hH33
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH31 : (47085991679408293422906130035 / 17179869184) ≤ H31 := by
    change (47085991679408293422906130035 / 17179869184) ≤ (47085991679408293422906130035 / 17179869184) + x * H32
    have hn : 0 ≤ H32 := (by norm_num : (0 : ℝ) ≤ (14967251271684309847212868905 / 17179869184)).trans hH32
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH30 : (494322457491160415398838822265 / 68719476736) ≤ H30 := by
    change (494322457491160415398838822265 / 68719476736) ≤ (494322457491160415398838822265 / 68719476736) + x * H31
    have hn : 0 ≤ H31 := (by norm_num : (0 : ℝ) ≤ (47085991679408293422906130035 / 17179869184)).trans hH31
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH29 : (1096865616264412628102337994125 / 68719476736) ≤ H29 := by
    change (1096865616264412628102337994125 / 68719476736) ≤ (1096865616264412628102337994125 / 68719476736) + x * H30
    have hn : 0 ≤ H30 := (by norm_num : (0 : ℝ) ≤ (494322457491160415398838822265 / 68719476736)).trans hH30
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH28 : (1038881666003184189295250584905 / 34359738368) ≤ H28 := by
    change (1038881666003184189295250584905 / 34359738368) ≤ (1038881666003184189295250584905 / 34359738368) + x * H29
    have hn : 0 ≤ H29 := (by norm_num : (0 : ℝ) ≤ (1096865616264412628102337994125 / 68719476736)).trans hH29
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH27 : (1691831816412658376468228661445 / 34359738368) ≤ H27 := by
    change (1691831816412658376468228661445 / 34359738368) ≤ (1691831816412658376468228661445 / 34359738368) + x * H28
    have hn : 0 ≤ H28 := (by norm_num : (0 : ℝ) ≤ (1038881666003184189295250584905 / 34359738368)).trans hH28
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH26 : (4760515745926218039704368553127 / 68719476736) ≤ H26 := by
    change (4760515745926218039704368553127 / 68719476736) ≤ (4760515745926218039704368553127 / 68719476736) + x * H27
    have hn : 0 ≤ H27 := (by norm_num : (0 : ℝ) ≤ (1691831816412658376468228661445 / 34359738368)).trans hH27
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH25 : (5804353176841532981321883608379 / 68719476736) ≤ H25 := by
    change (5804353176841532981321883608379 / 68719476736) ≤ (5804353176841532981321883608379 / 68719476736) + x * H26
    have hn : 0 ≤ H26 := (by norm_num : (0 : ℝ) ≤ (4760515745926218039704368553127 / 68719476736)).trans hH26
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH24 : (191960795758612309051793014845 / 2147483648) ≤ H24 := by
    change (191960795758612309051793014845 / 2147483648) ≤ (191960795758612309051793014845 / 2147483648) + x * H25
    have hn : 0 ≤ H25 := (by norm_num : (0 : ℝ) ≤ (5804353176841532981321883608379 / 68719476736)).trans hH25
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH23 : (705383967802599667627966765845 / 8589934592) ≤ H23 := by
    change (705383967802599667627966765845 / 8589934592) ≤ (705383967802599667627966765845 / 8589934592) + x * H24
    have hn : 0 ≤ H24 := (by norm_num : (0 : ℝ) ≤ (191960795758612309051793014845 / 2147483648)).trans hH24
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH22 : (4493744446333644603192568919715 / 68719476736) ≤ H22 := by
    change (4493744446333644603192568919715 / 68719476736) ≤ (4493744446333644603192568919715 / 68719476736) + x * H23
    have hn : 0 ≤ H23 := (by norm_num : (0 : ℝ) ≤ (705383967802599667627966765845 / 8589934592)).trans hH23
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH21 : (3092827225633815757330936868175 / 68719476736) ≤ H21 := by
    change (3092827225633815757330936868175 / 68719476736) ≤ (3092827225633815757330936868175 / 68719476736) + x * H22
    have hn : 0 ≤ H22 := (by norm_num : (0 : ℝ) ≤ (4493744446333644603192568919715 / 68719476736)).trans hH22
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH20 : (915531968958798455993178434985 / 34359738368) ≤ H20 := by
    change (915531968958798455993178434985 / 34359738368) ≤ (915531968958798455993178434985 / 34359738368) + x * H21
    have hn : 0 ≤ H21 := (by norm_num : (0 : ℝ) ≤ (3092827225633815757330936868175 / 68719476736)).trans hH21
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH19 : (463071706936827439189333479885 / 34359738368) ≤ H19 := by
    change (463071706936827439189333479885 / 34359738368) ≤ (463071706936827439189333479885 / 34359738368) + x * H20
    have hn : 0 ≤ H20 := (by norm_num : (0 : ℝ) ≤ (915531968958798455993178434985 / 34359738368)).trans hH20
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH18 : (396407978935978026727735030005 / 68719476736) ≤ H18 := by
    change (396407978935978026727735030005 / 68719476736) ≤ (396407978935978026727735030005 / 68719476736) + x * H19
    have hn : 0 ≤ H19 := (by norm_num : (0 : ℝ) ≤ (463071706936827439189333479885 / 34359738368)).trans hH19
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH17 : (141710219716635654189040480545 / 68719476736) ≤ H17 := by
    change (141710219716635654189040480545 / 68719476736) ≤ (141710219716635654189040480545 / 68719476736) + x * H18
    have hn : 0 ≤ H18 := (by norm_num : (0 : ℝ) ≤ (396407978935978026727735030005 / 68719476736)).trans hH18
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH16 : (10386960418361481105924858085 / 17179869184) ≤ H16 := by
    change (10386960418361481105924858085 / 17179869184) ≤ (10386960418361481105924858085 / 17179869184) + x * H17
    have hn : 0 ≤ H17 := (by norm_num : (0 : ℝ) ≤ (141710219716635654189040480545 / 68719476736)).trans hH17
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH15 : (2433642285701873657084816835 / 17179869184) ≤ H15 := by
    change (2433642285701873657084816835 / 17179869184) ≤ (2433642285701873657084816835 / 17179869184) + x * H16
    have hn : 0 ≤ H16 := (by norm_num : (0 : ℝ) ≤ (10386960418361481105924858085 / 17179869184)).trans hH16
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH14 : (1753372736041694954871295611 / 68719476736) ≤ H14 := by
    change (1753372736041694954871295611 / 68719476736) ≤ (1753372736041694954871295611 / 68719476736) + x * H15
    have hn : 0 ≤ H15 := (by norm_num : (0 : ℝ) ≤ (2433642285701873657084816835 / 17179869184)).trans hH15
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH13 : (228049802610181623903382551 / 68719476736) ≤ H13 := by
    change (228049802610181623903382551 / 68719476736) ≤ (228049802610181623903382551 / 68719476736) + x * H14
    have hn : 0 ≤ H14 := (by norm_num : (0 : ℝ) ≤ (1753372736041694954871295611 / 68719476736)).trans hH14
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH12 : (9536465342240896850557767 / 34359738368) ≤ H12 := by
    change (9536465342240896850557767 / 34359738368) ≤ (9536465342240896850557767 / 34359738368) + x * H13
    have hn : 0 ≤ H13 := (by norm_num : (0 : ℝ) ≤ (228049802610181623903382551 / 68719476736)).trans hH13
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH11 : (385331599068766703831387 / 34359738368) ≤ H11 := by
    change (385331599068766703831387 / 34359738368) ≤ (385331599068766703831387 / 34359738368) + x * H12
    have hn : 0 ≤ H12 := (by norm_num : (0 : ℝ) ≤ (9536465342240896850557767 / 34359738368)).trans hH12
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH10 : (131893858365231407445 / 68719476736) ≤ H10 := by
    change (131893858365231407445 / 68719476736) ≤ (131893858365231407445 / 68719476736) + x * H11
    have hn : 0 ≤ H11 := (by norm_num : (0 : ℝ) ≤ (385331599068766703831387 / 34359738368)).trans hH11
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH9 : (307752336185539950705 / 68719476736) ≤ H9 := by
    change (307752336185539950705 / 68719476736) ≤ (307752336185539950705 / 68719476736) + x * H10
    have hn : 0 ≤ H10 := (by norm_num : (0 : ℝ) ≤ (131893858365231407445 / 68719476736)).trans hH10
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH8 : (66262464728944008525 / 8589934592) ≤ H8 := by
    change (66262464728944008525 / 8589934592) ≤ (66262464728944008525 / 8589934592) + x * H9
    have hn : 0 ≤ H9 := (by norm_num : (0 : ℝ) ≤ (307752336185539950705 / 68719476736)).trans hH9
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH7 : (10760571195298599675 / 1073741824) ≤ H7 := by
    change (10760571195298599675 / 1073741824) ≤ (10760571195298599675 / 1073741824) + x * H8
    have hn : 0 ≤ H8 := (by norm_num : (0 : ℝ) ≤ (66262464728944008525 / 8589934592)).trans hH8
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH6 : (2658494060014948155 / 268435456) ≤ H6 := by
    change (2658494060014948155 / 268435456) ≤ (2658494060014948155 / 268435456) + x * H7
    have hn : 0 ≤ H7 := (by norm_num : (0 : ℝ) ≤ (10760571195298599675 / 1073741824)).trans hH7
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH5 : (7975482180044844465 / 1073741824) ≤ H5 := by
    change (7975482180044844465 / 1073741824) ≤ (7975482180044844465 / 1073741824) + x * H6
    have hn : 0 ≤ H6 := (by norm_num : (0 : ℝ) ≤ (2658494060014948155 / 268435456)).trans hH6
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH4 : (139920740000786745 / 33554432) ≤ H4 := by
    change (139920740000786745 / 33554432) ≤ (139920740000786745 / 33554432) + x * H5
    have hn : 0 ≤ H5 := (by norm_num : (0 : ℝ) ≤ (7975482180044844465 / 1073741824)).trans hH5
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH3 : (14277626530692525 / 8388608) ≤ H3 := by
    change (14277626530692525 / 8388608) ≤ (14277626530692525 / 8388608) + x * H4
    have hn : 0 ≤ H4 := (by norm_num : (0 : ℝ) ≤ (139920740000786745 / 33554432)).trans hH4
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH2 : (1002776445299475 / 2097152) ≤ H2 := by
    change (1002776445299475 / 2097152) ≤ (1002776445299475 / 2097152) + x * H3
    have hn : 0 ≤ H3 := (by norm_num : (0 : ℝ) ≤ (14277626530692525 / 8388608)).trans hH3
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH1 : (173814583851909 / 2097152) ≤ H1 := by
    change (173814583851909 / 2097152) ≤ (173814583851909 / 2097152) + x * H2
    have hn : 0 ≤ H2 := (by norm_num : (0 : ℝ) ≤ (1002776445299475 / 2097152)).trans hH2
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH0 : (1755702867191 / 262144) ≤ H0 := by
    change (1755702867191 / 262144) ≤ (1755702867191 / 262144) + x * H1
    have hn : 0 ≤ H1 := (by norm_num : (0 : ℝ) ≤ (173814583851909 / 2097152)).trans hH1
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hHpos : 0 ≤ H0 := (by norm_num : (0 : ℝ) ≤ (1755702867191 / 262144)).trans hH0
  have he : (1+x)^29 * student28Taylor 10 x ^ 2 - 1 = x ^ 11 * H0 := by
    dsimp only [H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, H28, H29, H30, H31, H32, H33, H34, H35, H36, H37, H38]
    simp only [student28Taylor, Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num [student28TaylorCoefficient]
    ring
  rw [he]
  exact mul_nonneg (pow_nonneg hx _) hHpos


/-- Finite square certificate for the degree-11 polynomial bounding the
actual t(28) kernel (T5(iii)), with a positive Horner remainder on [0,.06]. -/
theorem student28_square_certificate_11 {x : ℝ} (hx : 0 ≤ x) (hxu : x ≤ (3 : ℝ) / 50) :
    0 ≤ 1 - (1+x)^29 * student28Taylor 11 x ^ 2 := by
  let H39 : ℝ := (-3082492557862698184230481 / 274877906944)
  let H38 : ℝ := (-86624331677080314279293313 / 274877906944) + x * H39
  let H37 : ℝ := (-586510292592580694987850903 / 137438953472) + x * H38
  let H36 : ℝ := (-5095408383006824317870645665 / 137438953472) + x * H37
  let H35 : ℝ := (-63800169524789612517422005095 / 274877906944) + x * H36
  let H34 : ℝ := (-306502411430312016126868570455 / 274877906944) + x * H35
  let H33 : ℝ := (-293703304207996407789068343885 / 68719476736) + x * H34
  let H32 : ℝ := (-460988959601333095482969672435 / 34359738368) + x * H33
  let H31 : ℝ := (-9657321468888977986866128029665 / 274877906944) + x * H32
  let H30 : ℝ := (-21378129752045273295543642244785 / 274877906944) + x * H31
  let H29 : ℝ := (-20197669583946562976548518470505 / 137438953472) + x * H30
  let H28 : ℝ := (-32806240324533077725693625825115 / 137438953472) + x * H29
  let H27 : ℝ := (-92057345659538923452672372076735 / 274877906944) + x * H28
  let H26 : ℝ := (-111918012685634505864054981471759 / 274877906944) + x * H27
  let H25 : ℝ := (-7380095513784902898950219869701 / 17179869184) + x * H26
  let H24 : ℝ := (-27031764154202588476605072701265 / 68719476736) + x * H25
  let H23 : ℝ := (-85811710976773508355604795461915 / 274877906944) + x * H24
  let H22 : ℝ := (-58847300037303192712024645443435 / 274877906944) + x * H23
  let H21 : ℝ := (-17353335557313813630270144268185 / 137438953472) + x * H22
  let H20 : ℝ := (-8741659504229414323917963421815 / 137438953472) + x * H21
  let H19 : ℝ := (-7450967043253499049982044297405 / 274877906944) + x * H20
  let H18 : ℝ := (-2651393655133843256390669469645 / 274877906944) + x * H19
  let H17 : ℝ := (-193388658804926172687415806945 / 68719476736) + x * H18
  let H16 : ℝ := (-11268408646204224338582400915 / 17179869184) + x * H17
  let H15 : ℝ := (-32292580258755758826104637235 / 274877906944) + x * H16
  let H14 : ℝ := (-4174878726104292465704917731 / 274877906944) + x * H15
  let H13 : ℝ := (-173456890991860793156485191 / 137438953472) + x * H14
  let H12 : ℝ := (-6959654759683664877036653 / 137438953472) + x * H13
  let H11 : ℝ := (355303002574250758755 / 274877906944) + x * H12
  let H10 : ℝ := (1167424151315395350195 / 274877906944) + x * H11
  let H9 : ℝ := (339726604880141504025 / 34359738368) + x * H10
  let H8 : ℝ := (1167424151315395350195 / 68719476736) + x * H9
  let H7 : ℝ := (23632067840392618425 / 1073741824) + x * H8
  let H6 : ℝ := (23281963131646061115 / 1073741824) + x * H7
  let H5 : ℝ := (2175131503648593945 / 134217728) + x * H6
  let H4 : ℝ := (9730851463691078175 / 1073741824) + x * H5
  let H3 : ℝ := (30891591948225645 / 8388608) + x * H4
  let H2 : ℝ := (8634295886150025 / 8388608) + x * H3
  let H1 : ℝ := (185969449855539 / 1048576) + x * H2
  let H0 : ℝ := (29846948742247 / 2097152) + x * H1
  have hH39 : (-3082492557862698184230481 / 274877906944) ≤ H39 := by dsimp [H39]; norm_num
  have hH38 : (-4340464061527603808517357093 / 13743895347200) ≤ H38 := by
    change (-4340464061527603808517357093 / 13743895347200) ≤ (-86624331677080314279293313 / 274877906944) + x * H39
    have hp := mul_le_mul_of_nonneg_left hH39 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-3082492557862698184230481 / 274877906944) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH37 : (-2945572855147486286364806586279 / 687194767360000) ≤ H37 := by
    change (-2945572855147486286364806586279 / 687194767360000) ≤ (-586510292592580694987850903 / 137438953472) + x * H38
    have hp := mul_le_mul_of_nonneg_left hH38 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-4340464061527603808517357093 / 13743895347200) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH36 : (-1282688814317148538326755836008837 / 34359738368000000) ≤ H36 := by
    change (-1282688814317148538326755836008837 / 34359738368000000) ≤ (-5095408383006824317870645665 / 137438953472) + x * H37
    have hp := mul_le_mul_of_nonneg_left hH37 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-2945572855147486286364806586279 / 687194767360000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH35 : (-402599125972886523848867799351776511 / 1717986918400000000) ≤ H35 := by
    change (-402599125972886523848867799351776511 / 1717986918400000000) ≤ (-63800169524789612517422005095 / 274877906944) + x * H36
    have hp := mul_le_mul_of_nonneg_left hH36 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-1282688814317148538326755836008837 / 34359738368000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH34 : (-96989800949891164611193031665242829533 / 85899345920000000000) ≤ H34 := by
    change (-96989800949891164611193031665242829533 / 85899345920000000000) ≤ (-306502411430312016126868570455 / 274877906944) + x * H35
    have hp := mul_le_mul_of_nonneg_left hH35 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-402599125972886523848867799351776511 / 1717986918400000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH33 : (-18647425915849448980650350587808228488599 / 4294967296000000000000) ≤ H33 := by
    change (-18647425915849448980650350587808228488599 / 4294967296000000000000) ≤ (-293703304207996407789068343885 / 68719476736) + x * H34
    have hp := mul_le_mul_of_nonneg_left hH34 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-96989800949891164611193031665242829533 / 85899345920000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH32 : (-2937123275255880193710511504482174685465797 / 214748364800000000000000) ≤ H32 := by
    change (-2937123275255880193710511504482174685465797 / 214748364800000000000000) ≤ (-460988959601333095482969672435 / 34359738368) + x * H33
    have hp := mul_le_mul_of_nonneg_left hH33 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-18647425915849448980650350587808228488599 / 4294967296000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH31 : (-386050489704243343193089660672235586556397391 / 10737418240000000000000000) ≤ H31 := by
    change (-386050489704243343193089660672235586556397391 / 10737418240000000000000000) ≤ (-9657321468888977986866128029665 / 274877906944) + x * H32
    have hp := mul_le_mul_of_nonneg_left hH32 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-2937123275255880193710511504482174685465797 / 214748364800000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH30 : (-42912311141076154434937945241362409884669192173 / 536870912000000000000000000) ≤ H30 := by
    change (-42912311141076154434937945241362409884669192173 / 536870912000000000000000000) ≤ (-21378129752045273295543642244785 / 274877906944) + x * H31
    have hp := mul_le_mul_of_nonneg_left hH31 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-386050489704243343193089660672235586556397391 / 10737418240000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH29 : (-4073594274037791544661946349494595042154007576519 / 26843545600000000000000000000) ≤ H29 := by
    change (-4073594274037791544661946349494595042154007576519 / 26843545600000000000000000000) ≤ (-20197669583946562976548518470505 / 137438953472) + x * H30
    have hp := mul_le_mul_of_nonneg_left hH30 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-42912311141076154434937945241362409884669192173 / 536870912000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH28 : (-332594223491381711798962653746872457001462022729557 / 1342177280000000000000000000000) ≤ H28 := by
    change (-332594223491381711798962653746872457001462022729557 / 1342177280000000000000000000000) ≤ (-32806240324533077725693625825115 / 137438953472) + x * H29
    have hp := mul_le_mul_of_nonneg_left hH29 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-4073594274037791544661946349494595042154007576519 / 26843545600000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH27 : (-23472720575635015118959478800287248230379386068188671 / 67108864000000000000000000000000) ≤ H27 := by
    change (-23472720575635015118959478800287248230379386068188671 / 67108864000000000000000000000000) ≤ (-92057345659538923452672372076735 / 274877906944) + x * H28
    have hp := mul_le_mul_of_nonneg_left hH28 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-332594223491381711798962653746872457001462022729557 / 1342177280000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH26 : (-1436604840018341884517705846944794850159888158204566013 / 3355443200000000000000000000000000) ≤ H26 := by
    change (-1436604840018341884517705846944794850159888158204566013 / 3355443200000000000000000000000000) ≤ (-111918012685634505864054981471759 / 274877906944) + x * H27
    have hp := mul_le_mul_of_nonneg_left hH27 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-23472720575635015118959478800287248230379386068188671 / 67108864000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH25 : (-76381059771860718026113858455883212675479664474613698039 / 167772160000000000000000000000000000) ≤ H25 := by
    change (-76381059771860718026113858455883212675479664474613698039 / 167772160000000000000000000000000000) ≤ (-7380095513784902898950219869701 / 17179869184) + x * H26
    have hp := mul_le_mul_of_nonneg_left hH26 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-1436604840018341884517705846944794850159888158204566013 / 3355443200000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH24 : (-3528919077045390317726421739096287333338938993423841094117 / 8388608000000000000000000000000000000) ≤ H24 := by
    change (-3528919077045390317726421739096287333338938993423841094117 / 8388608000000000000000000000000000000) ≤ (-27031764154202588476605072701265 / 68719476736) + x * H25
    have hp := mul_le_mul_of_nonneg_left hH25 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-76381059771860718026113858455883212675479664474613698039 / 167772160000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH23 : (-141525036919816451036804746573970685730485566980271523282351 / 419430400000000000000000000000000000000) ≤ H23 := by
    change (-141525036919816451036804746573970685730485566980271523282351 / 419430400000000000000000000000000000000) ≤ (-85811710976773508355604795461915 / 274877906944) + x * H24
    have hp := mul_le_mul_of_nonneg_left hH24 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-3528919077045390317726421739096287333338938993423841094117 / 8388608000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH22 : (-4914267801593738347863271100335544259339894200940814569847053 / 20971520000000000000000000000000000000000) ≤ H22 := by
    change (-4914267801593738347863271100335544259339894200940814569847053 / 20971520000000000000000000000000000000000) ≤ (-58847300037303192712024645443435 / 274877906944) + x * H23
    have hp := mul_le_mul_of_nonneg_left hH23 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-141525036919816451036804746573970685730485566980271523282351 / 419430400000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH21 : (-147138246804697395694454561440845805141300932602822443709541159 / 1048576000000000000000000000000000000000000) ≤ H21 := by
    change (-147138246804697395694454561440845805141300932602822443709541159 / 1048576000000000000000000000000000000000000) ≤ (-17353335557313813630270144268185 / 137438953472) + x * H22
    have hp := mul_le_mul_of_nonneg_left hH22 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-4914267801593738347863271100335544259339894200940814569847053 / 20971520000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH20 : (-3776093201194966181497869994524182312884840297808467331128623477 / 52428800000000000000000000000000000000000000) ≤ H20 := by
    change (-3776093201194966181497869994524182312884840297808467331128623477 / 52428800000000000000000000000000000000000000) ≤ (-8741659504229414323917963421815 / 137438953472) + x * H21
    have hp := mul_le_mul_of_nonneg_left hH21 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-147138246804697395694454561440845805141300932602822443709541159 / 1048576000000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH19 : (-82386238618987683368693708950218741396662333393425401993385870431 / 2621440000000000000000000000000000000000000000) ≤ H19 := by
    change (-82386238618987683368693708950218741396662333393425401993385870431 / 2621440000000000000000000000000000000000000000) ≤ (-7450967043253499049982044297405 / 274877906944) + x * H20
    have hp := mul_le_mul_of_nonneg_left hH20 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-3776093201194966181497869994524182312884840297808467331128623477 / 52428800000000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH18 : (-1511441731648781314299935205927900029121627625180276205980157611293 / 131072000000000000000000000000000000000000000000) ≤ H18 := by
    change (-1511441731648781314299935205927900029121627625180276205980157611293 / 131072000000000000000000000000000000000000000000) ≤ (-2651393655133843256390669469645 / 274877906944) + x * H19
    have hp := mul_le_mul_of_nonneg_left hH19 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-82386238618987683368693708950218741396662333393425401993385870431 / 2621440000000000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH17 : (-22977304893597292723666846532796059706505507875540828617940472833879 / 6553600000000000000000000000000000000000000000000) ≤ H17 := by
    change (-22977304893597292723666846532796059706505507875540828617940472833879 / 6553600000000000000000000000000000000000000000000) ≤ (-193388658804926172687415806945 / 68719476736) + x * H18
    have hp := mul_le_mul_of_nonneg_left hH18 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-1511441731648781314299935205927900029121627625180276205980157611293 / 131072000000000000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH16 : (-283859752933893691269572334394378169353891523626622485853821418501637 / 327680000000000000000000000000000000000000000000000) ≤ H16 := by
    change (-283859752933893691269572334394378169353891523626622485853821418501637 / 327680000000000000000000000000000000000000000000000) ≤ (-11268408646204224338582400915 / 17179869184) + x * H17
    have hp := mul_le_mul_of_nonneg_left hH17 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-22977304893597292723666846532796059706505507875540828617940472833879 / 6553600000000000000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH15 : (-2776367034005609951287831370846994829106596445879867457561464255504911 / 16384000000000000000000000000000000000000000000000000) ≤ H15 := by
    change (-2776367034005609951287831370846994829106596445879867457561464255504911 / 16384000000000000000000000000000000000000000000000000) ≤ (-32292580258755758826104637235 / 274877906944) + x * H16
    have hp := mul_le_mul_of_nonneg_left hH16 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-283859752933893691269572334394378169353891523626622485853821418501637 / 327680000000000000000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH14 : (-20771209274505914055035243141104483938003383087639602372684392766514733 / 819200000000000000000000000000000000000000000000000000) ≤ H14 := by
    change (-20771209274505914055035243141104483938003383087639602372684392766514733 / 819200000000000000000000000000000000000000000000000000) ≤ (-4174878726104292465704917731 / 274877906944) + x * H15
    have hp := mul_le_mul_of_nonneg_left hH15 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-2776367034005609951287831370846994829106596445879867457561464255504911 / 16384000000000000000000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH13 : (-114007809680585325117034461520462347077682024262918807118053178299544199 / 40960000000000000000000000000000000000000000000000000000) ≤ H13 := by
    change (-114007809680585325117034461520462347077682024262918807118053178299544199 / 40960000000000000000000000000000000000000000000000000000) ≤ (-173456890991860793156485191 / 137438953472) + x * H14
    have hp := mul_le_mul_of_nonneg_left hH14 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-20771209274505914055035243141104483938003383087639602372684392766514733 / 819200000000000000000000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH12 : (-445730366469331338227707181639519670627577322788756421354159534898632597 / 2048000000000000000000000000000000000000000000000000000000) ≤ H12 := by
    change (-445730366469331338227707181639519670627577322788756421354159534898632597 / 2048000000000000000000000000000000000000000000000000000000) ≤ (-6959654759683664877036653 / 137438953472) + x * H13
    have hp := mul_le_mul_of_nonneg_left hH13 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-114007809680585325117034461520462347077682024262918807118053178299544199 / 40960000000000000000000000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH11 : (-1337058738725143590200166878900072988933513218366269264062478604695897791 / 102400000000000000000000000000000000000000000000000000000000) ≤ H11 := by
    change (-1337058738725143590200166878900072988933513218366269264062478604695897791 / 102400000000000000000000000000000000000000000000000000000000) ≤ (355303002574250758755 / 274877906944) + x * H12
    have hp := mul_le_mul_of_nonneg_left hH12 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-445730366469331338227707181639519670627577322788756421354159534898632597 / 2048000000000000000000000000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH10 : (-3989431246850003891257948362234658053714602155098807792187435814087693373 / 5120000000000000000000000000000000000000000000000000000000000) ≤ H10 := by
    change (-3989431246850003891257948362234658053714602155098807792187435814087693373 / 5120000000000000000000000000000000000000000000000000000000000) ≤ (1167424151315395350195 / 274877906944) + x * H11
    have hp := mul_le_mul_of_nonneg_left hH11 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-1337058738725143590200166878900072988933513218366269264062478604695897791 / 102400000000000000000000000000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH9 : (-9437133289971221485751887212405878458018806465296423376562307442263080119 / 256000000000000000000000000000000000000000000000000000000000000) ≤ H9 := by
    change (-9437133289971221485751887212405878458018806465296423376562307442263080119 / 256000000000000000000000000000000000000000000000000000000000000) ≤ (339726604880141504025 / 34359738368) + x * H10
    have hp := mul_le_mul_of_nonneg_left hH10 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-3989431246850003891257948362234658053714602155098807792187435814087693373 / 5120000000000000000000000000000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH8 : (189138293384355128968267083018391495485318580604110729870313077673210759643 / 12800000000000000000000000000000000000000000000000000000000000000) ≤ H8 := by
    change (189138293384355128968267083018391495485318580604110729870313077673210759643 / 12800000000000000000000000000000000000000000000000000000000000000) ≤ (1167424151315395350195 / 68719476736) + x * H9
    have hp := mul_le_mul_of_nonneg_left hH9 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-9437133289971221485751887212405878458018806465296423376562307442263080119 / 256000000000000000000000000000000000000000000000000000000000000) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH7 : (23632067840392618425 / 1073741824) ≤ H7 := by
    change (23632067840392618425 / 1073741824) ≤ (23632067840392618425 / 1073741824) + x * H8
    have hn : 0 ≤ H8 := (by norm_num : (0 : ℝ) ≤ (189138293384355128968267083018391495485318580604110729870313077673210759643 / 12800000000000000000000000000000000000000000000000000000000000000)).trans hH8
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH6 : (23281963131646061115 / 1073741824) ≤ H6 := by
    change (23281963131646061115 / 1073741824) ≤ (23281963131646061115 / 1073741824) + x * H7
    have hn : 0 ≤ H7 := (by norm_num : (0 : ℝ) ≤ (23632067840392618425 / 1073741824)).trans hH7
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH5 : (2175131503648593945 / 134217728) ≤ H5 := by
    change (2175131503648593945 / 134217728) ≤ (2175131503648593945 / 134217728) + x * H6
    have hn : 0 ≤ H6 := (by norm_num : (0 : ℝ) ≤ (23281963131646061115 / 1073741824)).trans hH6
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH4 : (9730851463691078175 / 1073741824) ≤ H4 := by
    change (9730851463691078175 / 1073741824) ≤ (9730851463691078175 / 1073741824) + x * H5
    have hn : 0 ≤ H5 := (by norm_num : (0 : ℝ) ≤ (2175131503648593945 / 134217728)).trans hH5
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH3 : (30891591948225645 / 8388608) ≤ H3 := by
    change (30891591948225645 / 8388608) ≤ (30891591948225645 / 8388608) + x * H4
    have hn : 0 ≤ H4 := (by norm_num : (0 : ℝ) ≤ (9730851463691078175 / 1073741824)).trans hH4
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH2 : (8634295886150025 / 8388608) ≤ H2 := by
    change (8634295886150025 / 8388608) ≤ (8634295886150025 / 8388608) + x * H3
    have hn : 0 ≤ H3 := (by norm_num : (0 : ℝ) ≤ (30891591948225645 / 8388608)).trans hH3
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH1 : (185969449855539 / 1048576) ≤ H1 := by
    change (185969449855539 / 1048576) ≤ (185969449855539 / 1048576) + x * H2
    have hn : 0 ≤ H2 := (by norm_num : (0 : ℝ) ≤ (8634295886150025 / 8388608)).trans hH2
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH0 : (29846948742247 / 2097152) ≤ H0 := by
    change (29846948742247 / 2097152) ≤ (29846948742247 / 2097152) + x * H1
    have hn : 0 ≤ H1 := (by norm_num : (0 : ℝ) ≤ (185969449855539 / 1048576)).trans hH1
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hHpos : 0 ≤ H0 := (by norm_num : (0 : ℝ) ≤ (29846948742247 / 2097152)).trans hH0
  have he : 1 - (1+x)^29 * student28Taylor 11 x ^ 2 = x ^ 12 * H0 := by
    dsimp only [H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, H28, H29, H30, H31, H32, H33, H34, H35, H36, H37, H38, H39]
    simp only [student28Taylor, Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num [student28TaylorCoefficient]
    ring
  rw [he]
  exact mul_nonneg (pow_nonneg hx _) hHpos


/-- The degree-10 upper polynomial is nonnegative on [0,.06], a needed
sign check when deriving an inequality from a square certificate (T5(iii)). -/
theorem student28_upper_polynomial_nonneg {x : ℝ} (hx : 0 ≤ x) (hxu : x ≤ (3 : ℝ) / 50) :
    0 ≤ student28Taylor 10 x := by
  let H10 : ℝ := (394137378349 / 262144)
  let H9 : ℝ := (-41929508335 / 65536) + x * H10
  let H8 : ℝ := (8385901667 / 32768) + x * H9
  let H7 : ℝ := (-195020969 / 2048) + x * H8
  let H6 : ℝ := (33296263 / 1024) + x * H7
  let H5 : ℝ := (-2561251 / 256) + x * H6
  let H4 : ℝ := (346115 / 128) + x * H5
  let H3 : ℝ := (-9889 / 16) + x * H4
  let H2 : ℝ := (899 / 8) + x * H3
  let H1 : ℝ := (-29 / 2) + x * H2
  let H0 : ℝ := 1 + x * H1
  have hH10 : (394137378349 / 262144) ≤ H10 := by dsimp [H10]; norm_num
  have hH9 : (-41929508335 / 65536) ≤ H9 := by
    change (-41929508335 / 65536) ≤ (-41929508335 / 65536) + x * H10
    have hn : 0 ≤ H10 := (by norm_num : (0 : ℝ) ≤ (394137378349 / 262144)).trans hH10
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH8 : (142560328339 / 655360) ≤ H8 := by
    change (142560328339 / 655360) ≤ (8385901667 / 32768) + x * H9
    have hp := mul_le_mul_of_nonneg_left hH9 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-41929508335 / 65536) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH7 : (-195020969 / 2048) ≤ H7 := by
    change (-195020969 / 2048) ≤ (-195020969 / 2048) + x * H8
    have hn : 0 ≤ H8 := (by norm_num : (0 : ℝ) ≤ (142560328339 / 655360)).trans hH8
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH6 : (2744563393 / 102400) ≤ H6 := by
    change (2744563393 / 102400) ≤ (33296263 / 1024) + x * H7
    have hp := mul_le_mul_of_nonneg_left hH7 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-195020969 / 2048) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH5 : (-2561251 / 256) ≤ H5 := by
    change (-2561251 / 256) ≤ (-2561251 / 256) + x * H6
    have hn : 0 ≤ H6 := (by norm_num : (0 : ℝ) ≤ (2744563393 / 102400)).trans hH6
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH4 : (26927747 / 12800) ≤ H4 := by
    change (26927747 / 12800) ≤ (346115 / 128) + x * H5
    have hp := mul_le_mul_of_nonneg_left hH5 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-2561251 / 256) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH3 : (-9889 / 16) ≤ H3 := by
    change (-9889 / 16) ≤ (-9889 / 16) + x * H4
    have hn : 0 ≤ H4 := (by norm_num : (0 : ℝ) ≤ (26927747 / 12800)).trans hH4
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH2 : (60233 / 800) ≤ H2 := by
    change (60233 / 800) ≤ (899 / 8) + x * H3
    have hp := mul_le_mul_of_nonneg_left hH3 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-9889 / 16) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hH1 : (-29 / 2) ≤ H1 := by
    change (-29 / 2) ≤ (-29 / 2) + x * H2
    have hn : 0 ≤ H2 := (by norm_num : (0 : ℝ) ≤ (60233 / 800)).trans hH2
    have hp := mul_nonneg hx hn
    exact le_add_of_nonneg_right hp
  have hH0 : (13 / 100) ≤ H0 := by
    change (13 / 100) ≤ 1 + x * H1
    have hp := mul_le_mul_of_nonneg_left hH1 hx
    have hn := mul_le_mul_of_nonpos_right hxu (by norm_num : (-29 / 2) ≤ (0 : ℝ))
    norm_num at hn
    linarith only [hp, hn]
  have hHpos : 0 ≤ H0 := (by norm_num : (0 : ℝ) ≤ (13 / 100)).trans hH0
  have he : student28Taylor 10 x = H0 := by
    dsimp only [H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10]
    simp only [student28Taylor, Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num [student28TaylorCoefficient]
    ring
  rwa [he]

/-- The squared polynomial certificates bound the actual half-integer-power
Student-t(28) kernel on [0,.06] (T5(iii)); no replacement of the density occurs. -/
theorem student28_kernel_bracket {x : ℝ} (hx : 0 ≤ x) (hxu : x ≤ (3 : ℝ) / 50) :
    student28Taylor 11 x ≤ (1 + x) ^ (-(29 / 2 : ℝ)) ∧
    (1 + x) ^ (-(29 / 2 : ℝ)) ≤ student28Taylor 10 x := by
  have hb : 0 < 1 + x := by linarith
  have hk : 0 ≤ (1 + x) ^ (-(29 / 2 : ℝ)) := Real.rpow_nonneg hb.le _
  have hden : 0 < (1 + x) ^ 29 := pow_pos hb _
  have hsq : ((1 + x) ^ (-(29 / 2 : ℝ))) ^ 2 * (1 + x) ^ 29 = 1 := by
    rw [← Real.rpow_natCast ((1 + x) ^ (-(29 / 2 : ℝ))) 2,
      ← Real.rpow_mul hb.le, ← Real.rpow_natCast (1 + x) 29, ← Real.rpow_add hb]
    norm_num
  have hupper := student28_square_certificate_10 hx hxu
  have hlower := student28_square_certificate_11 hx hxu
  have hp : 0 ≤ student28Taylor 10 x := student28_upper_polynomial_nonneg hx hxu
  constructor
  · have hm : student28Taylor 11 x ^ 2 * (1 + x) ^ 29 ≤
        ((1 + x) ^ (-(29 / 2 : ℝ))) ^ 2 * (1 + x) ^ 29 := by
      rw [hsq, mul_comm]
      linarith only [hlower]
    exact le_of_sq_le_sq ((mul_le_mul_iff_of_pos_right hden).mp hm) hk
  · have hm : ((1 + x) ^ (-(29 / 2 : ℝ))) ^ 2 * (1 + x) ^ 29 ≤
        student28Taylor 10 x ^ 2 * (1 + x) ^ 29 := by
      rw [hsq, mul_comm]
      linarith only [hupper]
    exact le_of_sq_le_sq ((mul_le_mul_iff_of_pos_right hden).mp hm) hp

/-- The t(28) polynomial certificate integrates to its finite rational series
(T5(iii)), so the subsequent decimal result is about the actual tail integral. -/
theorem student28_taylor_integral (n : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (∫ t in (0 : ℝ)..Real.sqrt q, student28Taylor n (t ^ 2 / 28)) =
      Real.sqrt q * student28IntegratedSeries n q := by
  let z := Real.sqrt q
  have hsq : z ^ 2 = q := Real.sq_sqrt hq
  have hint (k : Fin 12) :
      (∫ t in (0 : ℝ)..z, if k.val ≤ n then student28TaylorCoefficient k * (t ^ 2 / 28) ^ k.val else 0) =
        z * (if k.val ≤ n then student28TaylorCoefficient k * (q / 28) ^ k.val /
          (2 * k.val + 1 : ℕ) else 0) := by
    by_cases hk : k.val ≤ n
    · simp only [if_pos hk]
      have he : (fun t : ℝ => student28TaylorCoefficient k * (t ^ 2 / 28) ^ k.val) =
          (fun t : ℝ => (student28TaylorCoefficient k / (28 : ℝ) ^ k.val) * t ^ (2 * k.val)) := by
        funext t; rw [div_pow, ← pow_mul]; ring
      rw [he, intervalIntegral.integral_const_mul, integral_pow]
      simp only [zero_pow (by omega : 2 * k.val + 1 ≠ 0), sub_zero, pow_add, pow_one,
        pow_mul, hsq, div_pow]
      push_cast
      have hden : (2 * (k.val : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    · simp [hk]
  unfold student28Taylor student28IntegratedSeries
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact hint k
  · intro k hk
    by_cases hkn : k.val ≤ n
    · simp only [if_pos hkn]
      exact (by fun_prop : Continuous (fun t : ℝ =>
        student28TaylorCoefficient k * (t ^ 2 / 28) ^ k.val)).intervalIntegrable _ _
    · simp only [if_neg hkn]
      exact continuous_const.intervalIntegrable _ _

/-- Rigorous polynomial enclosure of the actual Student-t(28) p value
for 0≤q≤1.68 (T5(iii)); this includes every unadjusted statistic in the table. -/
theorem student28_p_enclosure {q : ℝ} (hq : 0 ≤ q) (hqmax : q ≤ (42 : ℝ) / 25) :
    1 - (student28Scale * Real.sqrt (q / 28)) * student28IntegratedSeries 10 q ≤
      studentReferenceP q 28 ∧
    studentReferenceP q 28 ≤
      1 - (student28Scale * Real.sqrt (q / 28)) * student28IntegratedSeries 11 q := by
  let C := student28Scale / (2 * Real.sqrt 28)
  have hC : 0 ≤ C := by dsimp [C, student28Scale]; positivity
  have hk : Continuous (fun t : ℝ => (1 + t ^ 2 / 28) ^ (-(29 / 2 : ℝ))) := by
    apply Continuous.rpow_const (by fun_prop)
    intro t; exact Or.inl (by positivity)
  have hT10 : Continuous (fun t : ℝ => student28Taylor 10 (t ^ 2 / 28)) := by
    unfold student28Taylor
    apply continuous_finsetSum
    intro k hk
    split_ifs <;> fun_prop
  have hT11 : Continuous (fun t : ℝ => student28Taylor 11 (t ^ 2 / 28)) := by
    unfold student28Taylor
    apply continuous_finsetSum
    intro k hk
    split_ifs <;> fun_prop
  have hdom (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.sqrt q)) : t ^ 2 / 28 ≤ (3 : ℝ) / 50 := by
    have hs := (sq_le_sq₀ ht.1 (Real.sqrt_nonneg q)).mpr ht.2
    rw [Real.sq_sqrt hq] at hs
    linarith
  have hl := intervalIntegral.integral_mono_on (μ := volume) (Real.sqrt_nonneg q)
    (hT11.intervalIntegrable _ _) (hk.intervalIntegrable _ _)
    (fun t ht => (student28_kernel_bracket (by positivity) (hdom t ht)).1)
  have hh := intervalIntegral.integral_mono_on (μ := volume) (Real.sqrt_nonneg q)
    (hk.intervalIntegrable _ _) (hT10.intervalIntegrable _ _)
    (fun t ht => (student28_kernel_bracket (by positivity) (hdom t ht)).2)
  rw [student28_taylor_integral 11 hq] at hl
  rw [student28_taylor_integral 10 hq] at hh
  have hP : studentReferenceP q 28 = 1 - (2 * C) *
      (∫ t in (0 : ℝ)..Real.sqrt q, (1 + t ^ 2 / 28) ^ (-(29 / 2 : ℝ))) := by
    unfold studentReferenceP
    simp_rw [student28_density_identity]
    rw [intervalIntegral.integral_const_mul]
    dsimp [C]
    ring
  have hm : (2 * C) * Real.sqrt q = student28Scale * Real.sqrt (q / 28) := by
    rw [Real.sqrt_div hq]
    dsimp [C]
    ring
  have hcl := mul_le_mul_of_nonneg_left hl (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
  have hch := mul_le_mul_of_nonneg_left hh (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
  rw [← mul_assoc, hm] at hcl hch
  rw [hP]
  constructor <;> linarith

/-- Finite rational decimal-certificate wrapper for t(28) p values (T5(iii)).
Its analytic premise is proved by the polynomial square certificates. -/
theorem student28_decimal_certificate {q alo ahi plo phi : ℝ}
    (hq : 0 ≤ q) (hqmax : q ≤ (42 : ℝ) / 25)
    (halopos : 0 ≤ alo) (hahipos : 0 ≤ ahi)
    (halosq : alo ^ 2 < student28Scale ^ 2 * (q / 28))
    (hahisq : student28Scale ^ 2 * (q / 28) < ahi ^ 2)
    (hs11 : 0 ≤ student28IntegratedSeries 11 q) (hs10 : 0 ≤ student28IntegratedSeries 10 q)
    (hplo : plo < 1 - ahi * student28IntegratedSeries 10 q)
    (hphi : 1 - alo * student28IntegratedSeries 11 q < phi) :
    plo < studentReferenceP q 28 ∧ studentReferenceP q 28 < phi := by
  let B := student28Scale * Real.sqrt (q / 28)
  have hB0 : 0 ≤ B := by dsimp [B, student28Scale]; positivity
  have hBsq : B ^ 2 = student28Scale ^ 2 * (q / 28) := by
    dsimp [B]; rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q / 28)]
  have haLo : alo < B := by rw [← hBsq] at halosq; nlinarith
  have haHi : B < ahi := by rw [← hBsq] at hahisq; nlinarith
  have he := student28_p_enclosure hq hqmax
  change 1 - B * student28IntegratedSeries 10 q ≤ _ ∧ _ ≤ 1 - B * student28IntegratedSeries 11 q at he
  have hmhi := mul_le_mul_of_nonneg_right haHi.le hs10
  have hmlo := mul_le_mul_of_nonneg_right haLo.le hs11
  constructor <;> linarith [he.1, he.2]

/-- P040-T5(iii): the two smallest reference values, both from unadjusted
bulk sales, have the printed target's narrow brackets. The t(28) bound follows
from a finite polynomial certificate. -/
theorem smallest_reference_p_bounds :
    (22533 / 100000 : ℝ) < studentReferenceP (tableSquaredStatistic false 1) 28 ∧
    studentReferenceP (tableSquaredStatistic false 1) 28 < (22534 / 100000 : ℝ) ∧
    (21504 / 100000 : ℝ) < normalReferenceP (tableSquaredStatistic false 1) ∧
    normalReferenceP (tableSquaredStatistic false 1) < (21505 / 100000 : ℝ) := by
  have ht := student28_decimal_certificate (q := tableSquaredStatistic false 1)
    (alo := 98042750 / 100000000) (ahi := 98042753 / 100000000)
    (plo := 22533 / 100000) (phi := 22534 / 100000)
    (by norm_num [tableSquaredStatistic]) (by norm_num [tableSquaredStatistic])
    (by norm_num) (by norm_num)
    (by norm_num [tableSquaredStatistic, student28Scale])
    (by norm_num [tableSquaredStatistic, student28Scale])
    (by
      simp only [student28IntegratedSeries, Fin.sum_univ_succ, Fin.sum_univ_zero]
      norm_num [student28TaylorCoefficient, tableSquaredStatistic])
    (by
      simp only [student28IntegratedSeries, Fin.sum_univ_succ, Fin.sum_univ_zero]
      norm_num [student28TaylorCoefficient, tableSquaredStatistic])
    (by
      simp only [student28IntegratedSeries, Fin.sum_univ_succ, Fin.sum_univ_zero]
      norm_num [student28TaylorCoefficient, tableSquaredStatistic])
    (by
      simp only [student28IntegratedSeries, Fin.sum_univ_succ, Fin.sum_univ_zero]
      norm_num [student28TaylorCoefficient, tableSquaredStatistic])
  have hn := normal_decimal_certificate (q := tableSquaredStatistic false 1)
    (alo := 9892185 / 10000000) (ahi := 9892189 / 10000000)
    (plo := 21504 / 100000) (phi := 21505 / 100000)
    (by norm_num [tableSquaredStatistic]) (by norm_num [tableSquaredStatistic])
    (by norm_num) (by norm_num)
    (by norm_num [tableSquaredStatistic]) (by norm_num [tableSquaredStatistic])
    (by norm_num [normalIntegratedSeries, Finset.sum_range_succ, normalTaylorError, Nat.factorial, tableSquaredStatistic])
    (by norm_num [normalIntegratedSeries, Finset.sum_range_succ, normalTaylorError, Nat.factorial, tableSquaredStatistic])
    (by norm_num [normalIntegratedSeries, Finset.sum_range_succ, normalTaylorError, Nat.factorial, tableSquaredStatistic])
  exact ⟨ht.1, ht.2, hn.1, hn.2⟩

/-- P040-T5(iii): unadjusted bulk sales gives the minimum p value among the
eight regressions for each reference, including the different Student-t degrees
of freedom of the two specifications. -/
theorem unadjusted_bulk_minimizes_reference_p (a : Bool) (o : Fin 4) :
    studentReferenceP (tableSquaredStatistic false 1) 28 ≤
      studentReferenceP (tableSquaredStatistic a o) (if a then 21 else 28) ∧
    normalReferenceP (tableSquaredStatistic false 1) ≤
      normalReferenceP (tableSquaredStatistic a o) := by
  have hq0 := (table_statistics_bounded.2 a o).1.le
  constructor
  · have hbulkhi := smallest_reference_p_bounds.2.1
    cases a
    · by_cases ho : o = 1
      · subst o; exact le_rfl
      · have hsmall : tableSquaredStatistic false o ≤ (3 : ℝ) / 5 := by
          fin_cases o <;> norm_num [tableSquaredStatistic] at *
        have ht := student28_decimal_certificate (q := 3 / 5)
          (alo := 6125462 / 10000000) (ahi := 6125463 / 10000000)
          (plo := 4 / 10) (phi := 5 / 10)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num [student28Scale]) (by norm_num [student28Scale])
          (by simp only [student28IntegratedSeries, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num [student28TaylorCoefficient])
          (by simp only [student28IntegratedSeries, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num [student28TaylorCoefficient])
          (by simp only [student28IntegratedSeries, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num [student28TaylorCoefficient])
          (by simp only [student28IntegratedSeries, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num [student28TaylorCoefficient])
        have hm := student_reference_antitone hq0 hsmall (by norm_num : (0 : ℝ) < 28)
        change studentReferenceP (tableSquaredStatistic false 1) 28 ≤
          studentReferenceP (tableSquaredStatistic false o) 28
        linarith [ht.1]
    · have hsmall : tableSquaredStatistic true o ≤ bulkSquaredStatistic := by
        fin_cases o <;> norm_num [tableSquaredStatistic, cafeSquaredStatistic, bulkSquaredStatistic]
      have hm := student_reference_antitone hq0 hsmall (by norm_num : (0 : ℝ) < 21)
      have hbulk21 := corrected_student_reference_bounds.2.2.1
      change studentReferenceP (tableSquaredStatistic false 1) 28 ≤
        studentReferenceP (tableSquaredStatistic true o) 21
      linarith
  · exact normal_reference_antitone hq0 (table_statistics_bounded.2 a o).2

/-- "q=beta_hat_T²/v" for each of the two recorded specifications (targets
S7; Table 1 p.5). This reuses the actual OLS/HC1 definitions, not witness numbers. -/
def recordedSquaredStatistic (a : Bool) (o : Fin 4) : ℝ :=
  if a then olsSquaredStatistic adjustedDesign (tableOutcome o) 1
  else olsSquaredStatistic unadjustedDesign (tableOutcome o) 1

/-- "the model's residual degrees of freedom" (corrected Methods, T5(i)):
the number of recorded rows minus the actual design rank. -/
def recordedResidualDF (a : Bool) : ℝ :=
  if a then (30 - originalAdjustedDesign.rank : ℕ) else (30 - unadjustedDesign.rank : ℕ)

/-- The exact table witnesses are the actual recorded statistics (T4/T5). -/
theorem recorded_statistic_identity (a : Bool) (o : Fin 4) :
    recordedSquaredStatistic a o = tableSquaredStatistic a o := by
  cases a
  · exact unadjusted_squared_statistics_certificate o
  · exact adjusted_squared_statistics_certificate o

/-- The actual residual degrees of freedom are 28 and 21 (T5(i)). -/
theorem recorded_df_identity (a : Bool) : recordedResidualDF a = if a then 21 else 28 := by
  have hu := corrected_regression_degrees_of_freedom.2.2.2.2.1
  have ha := corrected_regression_degrees_of_freedom.2.2.2.2.2
  cases a <;> simp [recordedResidualDF, hu, ha]

/-- P040-T4, the counterexample on the actual recorded regressions: their
normal-reference p values round to .58 and .28, excluding the printed .59 and
.29. All rows, coefficients, HC1 variances and tail integrals are connected by
proved identities in this file. -/
theorem recorded_normal_counterexample :
    pValueRoundsTwo (normalReferenceP (recordedSquaredStatistic true 2)) (58 / 100) ∧
    ¬pValueRoundsTwo (normalReferenceP (recordedSquaredStatistic true 2)) (59 / 100) ∧
    pValueRoundsTwo (normalReferenceP (recordedSquaredStatistic true 1)) (28 / 100) ∧
    ¬pValueRoundsTwo (normalReferenceP (recordedSquaredStatistic true 1)) (29 / 100) := by
  rw [recorded_statistic_identity, recorded_statistic_identity]
  simpa [tableSquaredStatistic] using normal_reference_rounding_mismatch

/-- P040-T5(ii), the corrected reference on the actual recorded regressions:
Student-t with the model's residual degrees of freedom gives the printed .59
and .29. This states the reference calculation, not an exact null law. -/
theorem recorded_corrected_p_values :
    pValueRoundsTwo (studentReferenceP (recordedSquaredStatistic true 2) (recordedResidualDF true)) (59 / 100) ∧
    pValueRoundsTwo (studentReferenceP (recordedSquaredStatistic true 1) (recordedResidualDF true)) (29 / 100) := by
  rw [recorded_statistic_identity, recorded_statistic_identity, recorded_df_identity]
  simpa [tableSquaredStatistic] using corrected_student_reference_rounding

/-- P040-T5(iii), the paper's significance statement for the actual eight
regressions: both references give two-tailed p>.10, with 28 or 21 residual
degrees of freedom as appropriate for the Student-t reference. -/
theorem recorded_effects_not_significant (a : Bool) (o : Fin 4) :
    (1 : ℝ) / 10 < studentReferenceP (recordedSquaredStatistic a o) (recordedResidualDF a) ∧
    (1 : ℝ) / 10 < normalReferenceP (recordedSquaredStatistic a o) := by
  rw [recorded_statistic_identity, recorded_df_identity]
  exact table_effects_not_significant a o

/-- One-decimal rounding for coefficients and standard errors in Table 1
(paper p.5; targets S5), using the same half-open rounding convention as S7. -/
def saleRoundsOne (x w : ℝ) : Prop := w - 1 / 20 ≤ x ∧ x < w + 1 / 20

/-- P040-T4 B1–B2: the exact adjusted coefficient/HC1-standard-error witnesses
round to the Table 1 treatment entries -8.9 (SE 16.2) and 23.2 (SE 21.2). -/
theorem recorded_table_cells_round :
    saleRoundsOne cafeCoefficientWitness (-89 / 10) ∧
    saleRoundsOne (Real.sqrt cafeVarianceWitness) (162 / 10) ∧
    saleRoundsOne bulkCoefficientWitness (232 / 10) ∧
    saleRoundsOne (Real.sqrt bulkVarianceWitness) (212 / 10) := by
  refine ⟨by norm_num [saleRoundsOne, cafeCoefficientWitness], ?_,
    by norm_num [saleRoundsOne, bulkCoefficientWitness], ?_⟩
  · unfold saleRoundsOne
    constructor
    · apply (Real.le_sqrt (by norm_num) regression_witness_arithmetic.1.le).mpr
      norm_num [cafeVarianceWitness]
    · apply (Real.sqrt_lt regression_witness_arithmetic.1.le (by norm_num)).mpr
      norm_num [cafeVarianceWitness]
  · unfold saleRoundsOne
    constructor
    · apply (Real.le_sqrt (by norm_num) regression_witness_arithmetic.2.1.le).mpr
      norm_num [bulkVarianceWitness]
    · apply (Real.sqrt_lt regression_witness_arithmetic.2.1.le (by norm_num)).mpr
      norm_num [bulkVarianceWitness]

end
end AronowAudit.P040

