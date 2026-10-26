/-
Upstream project: Causalean / CausalSmith.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.P010.Wave1.Gap.GP010P033B2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
Proofs for P033-T6 and P033-T7, with exact arithmetic certificates.
-/
namespace AronowAudit.P033.Wave1

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section

namespace binary_standardization

/-- A rational interval and its mathematical interpretation. -/
structure Interval where
  lo : ℚ
  hi : ℚ
  ordered : lo ≤ hi

def Interval.Contains (I : Interval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/- The Gaussian integral series lemmas in this namespace adapt
the `CausalSmith/Causalean` module `Mathlib.Probability.Certified.NormalCDF.PowerSeries`,
commit a7085d88d2e4b30003db7097ca374f4718da0f01 (Apache-2.0).
Only the required series lemmas are copied; normalization uses Mathlib's
proved twenty-decimal bounds for pi.
See NOTICE at the repository root.
-/
/-- The magnitude of the `k`th integrated Gaussian-series term at `x`, namely `x` to the power
`2k+1` divided by `2^k k! (2k+1)`. It is nonnegative for nonnegative `x`, which is how it is used; for
negative `x` the same formula is negative. -/
noncomputable def gaussianIntegralMagnitude (x : ℝ) (k : ℕ) : ℝ :=
  x ^ (2 * k + 1) /
    ((2 : ℝ) ^ k * (k.factorial : ℝ) * (2 * k + 1 : ℕ))

/-- The `k`th function in the power series for `exp (-t²/2)`. -/
noncomputable def gaussianIntegrandTerm (k : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * t ^ (2 * k) /
    ((2 : ℝ) ^ k * (k.factorial : ℝ))

/-- At every real argument, the Gaussian integrand is the sum of its classical
everywhere-convergent power series. -/
theorem gaussianIntegrand_hasSum (t : ℝ) :
    HasSum (fun k => gaussianIntegrandTerm k t)
      (Real.exp (-(t ^ 2) / 2)) := by
  rw [Real.exp_eq_exp_ℝ]
  have hfun : (fun k => gaussianIntegrandTerm k t) =
      (fun k => ((k.factorial : ℝ)⁻¹ • (-(t ^ 2) / 2) ^ k)) := by
    funext k
    simp [gaussianIntegrandTerm, div_pow]
    ring
  rw [hfun]
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (x := (-(t ^ 2) / 2 : ℝ))

/-- Integrating one Gaussian power-series term from zero to a real
endpoint gives the corresponding signed integrated-series coefficient. -/
theorem gaussianIntegrandTerm_integral (x : ℝ) (k : ℕ) :
    (∫ t in (0 : ℝ)..x, gaussianIntegrandTerm k t) =
      (-1 : ℝ) ^ k * gaussianIntegralMagnitude x k := by
  unfold gaussianIntegrandTerm gaussianIntegralMagnitude
  simp_rw [div_eq_mul_inv]
  rw [show (fun t : ℝ => (-1) ^ k * t ^ (2 * k) *
      (2 ^ k * (k.factorial : ℝ))⁻¹) =
      (fun t : ℝ => ((-1) ^ k * (2 ^ k * (k.factorial : ℝ))⁻¹) *
        t ^ (2 * k)) by
    funext t
    ring]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp
  ring

/-- On `[0,x]`, the norm of one Gaussian-series function is bounded by the
same unsigned monomial evaluated at the right endpoint. -/
theorem gaussianIntegrandTerm_norm_le (x : ℝ) (k : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) x) :
    ‖gaussianIntegrandTerm k t‖ ≤
      x ^ (2 * k) / ((2 : ℝ) ^ k * (k.factorial : ℝ)) := by
  -- Expand the norm and use `0 ≤ t ≤ x` to compare the even powers.
  have habs : |t| ≤ x := by simpa [abs_of_nonneg ht.1] using ht.2
  have hp : |t| ^ (2 * k) ≤ x ^ (2 * k) :=
    pow_le_pow_left₀ (abs_nonneg t) habs _
  have hden : 0 ≤ (2 : ℝ) ^ k * (k.factorial : ℝ) := by positivity
  rw [gaussianIntegrandTerm, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
    abs_pow, abs_of_nonneg hden, abs_neg, abs_one, one_pow, one_mul]
  exact div_le_div_of_nonneg_right hp hden

/-- The endpoint majorants for the Gaussian integrand's power series are
summable for every fixed real endpoint. -/
theorem gaussianIntegrandMajorant_summable (x : ℝ) :
    Summable (fun k =>
      x ^ (2 * k) / ((2 : ℝ) ^ k * (k.factorial : ℝ))) := by
  -- Identify this nonnegative series with the absolute exponential series at
  -- `x²/2`, using `Real.summable_pow_div_factorial`.
  refine (Real.summable_pow_div_factorial (x ^ 2 / 2)).congr ?_
  intro k
  rw [div_pow, ← pow_mul]
  ring

/-- The exact rational `k`th signed term in the integrated Gaussian power
series at the rational endpoint `x`. -/
def gaussianIntegralTerm (x : ℚ) (k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * x ^ (2 * k + 1) /
    ((2 : ℚ) ^ k * (k.factorial : ℚ) * (2 * k + 1 : ℕ))

/-- The exact rational Gaussian-integral partial sum through degree index `n`. -/
def gaussianIntegralPartial (x : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), gaussianIntegralTerm x k

/-- The alternating enclosure is the rational interval whose endpoints are two
consecutive Gaussian-integral partial sums. -/
def gaussianIntegralInterval (x : ℚ) (n : ℕ) : Interval :=
  ⟨min (gaussianIntegralPartial x n) (gaussianIntegralPartial x (n + 1)),
    max (gaussianIntegralPartial x n) (gaussianIntegralPartial x (n + 1)),
    min_le_max⟩

/-- For a nonnegative endpoint, all unsigned Gaussian-series coefficients are
nonnegative. -/
theorem gaussianIntegralMagnitude_nonneg (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ gaussianIntegralMagnitude x k := by
  -- Unfold; every factor in the numerator and denominator is nonnegative and
  -- the natural-number factors in the denominator are strictly positive.
  unfold gaussianIntegralMagnitude
  positivity

/-- If `x² ≤ 2(n+2)`, the coefficient magnitudes decrease at every index after
the partial sum boundary `n`. -/
theorem gaussianIntegralMagnitude_antitone_from (x : ℝ) (hx : 0 ≤ x) (n : ℕ)
    (hmono : x ^ 2 ≤ 2 * (n + 2 : ℕ)) :
    ∀ k, n + 1 ≤ k →
      gaussianIntegralMagnitude x (k + 1) ≤ gaussianIntegralMagnitude x k := by
  intro k hk
  have hk' : n + 2 ≤ k + 1 := by omega
  have hbound : x ^ 2 ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
    apply hmono.trans
    exact_mod_cast Nat.mul_le_mul_left 2 hk'
  have h₁ : x ^ 2 / (2 * (k + 1 : ℕ)) ≤ (1 : ℝ) :=
    (div_le_one (by positivity)).2 hbound
  have h₁nonneg : 0 ≤ x ^ 2 / (2 * (k + 1 : ℕ) : ℝ) := by positivity
  have h₂ : ((2 * k + 1 : ℕ) : ℝ) / (2 * k + 3 : ℕ) ≤ (1 : ℝ) := by
    apply (div_le_one (by positivity)).2
    norm_num
  have h₂nonneg : 0 ≤ ((2 * k + 1 : ℕ) : ℝ) / (2 * k + 3 : ℕ) := by positivity
  have hid :
      gaussianIntegralMagnitude x (k + 1) =
        gaussianIntegralMagnitude x k *
          (x ^ 2 / (2 * (k + 1 : ℕ))) *
          (((2 * k + 1 : ℕ) : ℝ) / (2 * k + 3 : ℕ)) := by
    unfold gaussianIntegralMagnitude
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [hid]
  have hm := gaussianIntegralMagnitude_nonneg x hx k
  calc
    gaussianIntegralMagnitude x k * (x ^ 2 / (2 * ↑(k + 1))) *
        (↑(2 * k + 1) / ↑(2 * k + 3)) ≤
      gaussianIntegralMagnitude x k * 1 * (↑(2 * k + 1) / ↑(2 * k + 3)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₁ hm) h₂nonneg
    _ ≤ gaussianIntegralMagnitude x k * 1 :=
        by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left h₂ (mul_nonneg hm zero_le_one)
    _ = gaussianIntegralMagnitude x k := by ring

/-- The signed integrated Gaussian coefficients sum to the exact Gaussian
integral on every finite nonnegative interval. -/
theorem gaussianIntegral_hasSum (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fun k => (-1 : ℝ) ^ k * gaussianIntegralMagnitude x k)
      (∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2) / 2)) := by
  -- Use the Gaussian power series and summable sup norms to justify termwise
  -- integration on `[0,x]`, then integrate monomials.
  -- Termwise integration uses `intervalIntegral.hasSum_intervalIntegral_of_summable_norm`.
  let f : ℕ → C(ℝ, ℝ) := fun k =>
    ⟨gaussianIntegrandTerm k, by
      unfold gaussianIntegrandTerm
      fun_prop⟩
  have hnorm : Summable (fun k =>
      ‖(f k).restrict
        (⟨Set.uIcc (0 : ℝ) x, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => ?_) (gaussianIntegrandMajorant_summable x)
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro t
    change ‖gaussianIntegrandTerm k t‖ ≤ _
    simpa only [ContinuousMap.restrict_apply] using
      gaussianIntegrandTerm_norm_le x k
        (by simpa [Set.uIcc_of_le hx] using t.property)
  have hi := intervalIntegral.hasSum_intervalIntegral_of_summable_norm hnorm
  have hterms : (fun k => ∫ t in (0 : ℝ)..x, f k t) =
      (fun k => (-1 : ℝ) ^ k * gaussianIntegralMagnitude x k) := by
    funext k
    change (∫ t in (0 : ℝ)..x, gaussianIntegrandTerm k t) = _
    exact gaussianIntegrandTerm_integral x k
  rw [hterms] at hi
  rw [show (∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2) / 2)) =
      ∫ t in (0 : ℝ)..x, ∑' k, f k t by
    apply intervalIntegral.integral_congr
    intro t _
    change Real.exp (-(t ^ 2) / 2) = ∑' k, gaussianIntegrandTerm k t
    exact (gaussianIntegrand_hasSum t).tsum_eq.symm]
  exact hi

/-- At a nonnegative rational endpoint `x`, if `x ^ 2 ≤ 2 * (n + 2)`,
two consecutive rational Gaussian-series partial sums enclose the
unnormalised Gaussian integral. -/
theorem gaussianIntegralInterval_sound (x : ℚ) (hx : 0 ≤ x) (n : ℕ)
    (hmono : x ^ 2 ≤ 2 * (n + 2 : ℕ)) :
    (gaussianIntegralInterval x n).Contains
      (∫ t in (0 : ℝ)..(x : ℝ), Real.exp (-(t ^ 2) / 2)) := by
  have hxR : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hmonoR : (x : ℝ) ^ 2 ≤ 2 * ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast hmono
  let a : ℕ → ℝ := fun k => gaussianIntegralMagnitude (x : ℝ) k
  let s : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * a k
  have hs : HasSum s (∫ t in (0 : ℝ)..(x : ℝ), Real.exp (-(t ^ 2) / 2)) := by
    exact gaussianIntegral_hasSum (x : ℝ) hxR
  have ha : Summable a := by
    have habs : Summable (fun k => ‖s k‖) := hs.summable.norm
    apply habs.congr
    intro k
    simp only [s, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_of_nonneg (gaussianIntegralMagnitude_nonneg (x : ℝ) hxR k), a]
  have hanti := gaussianIntegralMagnitude_antitone_from (x : ℝ) hxR n hmonoR
  have hb : Summable (fun j => a (j + (n + 1))) :=
    (summable_nat_add_iff (n + 1)).2 ha
  have hbanti : Antitone (fun j => a (j + (n + 1))) := by
    refine antitone_nat_of_succ_le ?_
    intro j
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hanti (j + (n + 1)) (by omega)
  let r : ℝ := ∑' j, (-1 : ℝ) ^ j * a (j + (n + 1))
  have hr_tendsto := hb.tendsto_alternating_series_tsum
  have hr0 : 0 ≤ r := by
    have h := hbanti.alternating_series_le_tendsto hr_tendsto 0
    exact h
  have hrle : r ≤ a (n + 1) := by
    have h := hbanti.tendsto_le_alternating_series hr_tendsto 0
    simpa [r] using h
  have htail : (∑' j, s (j + (n + 1))) = (-1 : ℝ) ^ (n + 1) * r := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    simp only [s, pow_add]
    ring
  have hsplit := hs.summable.sum_add_tsum_nat_add (n + 1)
  rw [hs.tsum_eq, htail] at hsplit
  have hrepresentation :
      (∫ t in (0 : ℝ)..(x : ℝ), Real.exp (-(t ^ 2) / 2)) =
        (∑ k ∈ Finset.range (n + 1), s k) + (-1 : ℝ) ^ (n + 1) * r :=
    hsplit.symm
  have hterm_cast (k : ℕ) :
      ((gaussianIntegralTerm x k : ℚ) : ℝ) = s k := by
    simp only [gaussianIntegralTerm, gaussianIntegralMagnitude, s, a]
    push_cast
    ring
  have hpartial_cast (m : ℕ) :
      ((gaussianIntegralPartial x m : ℚ) : ℝ) =
        ∑ k ∈ Finset.range (m + 1), s k := by
    simp only [gaussianIntegralPartial, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm_cast k
  have hnext_cast : ((gaussianIntegralPartial x (n + 1) : ℚ) : ℝ) =
      (∑ k ∈ Finset.range (n + 1), s k) + (-1 : ℝ) ^ (n + 1) * a (n + 1) := by
    rw [hpartial_cast]
    simpa only [Nat.add_assoc] using
      (Finset.sum_range_succ s (n + 1))
  rw [gaussianIntegralInterval, Interval.Contains, Rat.cast_min, Rat.cast_max,
    hpartial_cast, hnext_cast]
  obtain heven | hodd := Nat.even_or_odd (n + 1)
  · have hsign : (-1 : ℝ) ^ (n + 1) = 1 := by
      simpa using heven.neg_one_pow
    rw [hsign, one_mul] at hrepresentation ⊢
    constructor
    · apply min_le_iff.mpr
      left
      linarith
    · apply le_max_iff.mpr
      right
      linarith
  · have hsign : (-1 : ℝ) ^ (n + 1) = -1 := by
      simpa using hodd.neg_one_pow
    rw [hsign, neg_one_mul] at hrepresentation ⊢
    constructor
    · apply min_le_iff.mpr
      right
      linarith
    · apply le_max_iff.mpr
      left
      linarith


lemma density_scale_bounds :
    (39894228040143267793/10^20 : ℝ) ≤ 1 / Real.sqrt (2 * Real.pi) ∧
    1 / Real.sqrt (2 * Real.pi) ≤ (39894228040143267795/10^20 : ℝ) := by
  have hr : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hlo := Real.pi_gt_d20
  have hhi := Real.pi_lt_d20
  constructor
  · apply (le_div_iff₀ hr).2
    have hsq : ((39894228040143267793/10^20 : ℝ) * Real.sqrt (2 * Real.pi))^2 ≤ 1 := by
      rw [mul_pow, hs]
      nlinarith
    nlinarith [sq_nonneg ((39894228040143267793/10^20 : ℝ) * Real.sqrt (2 * Real.pi) - 1)]
  · apply (div_le_iff₀ hr).2
    have hsq : 1 ≤ ((39894228040143267795/10^20 : ℝ) * Real.sqrt (2 * Real.pi))^2 := by
      rw [mul_pow, hs]
      nlinarith
    have hpos : 0 ≤ (39894228040143267795/10^20 : ℝ) * Real.sqrt (2 * Real.pi) := by positivity
    nlinarith [sq_nonneg ((39894228040143267795/10^20 : ℝ) * Real.sqrt (2 * Real.pi) - 1)]

lemma cdf_integral (x : ℝ) :
    normalCDF x = 1/2 + (1 / Real.sqrt (2*Real.pi)) *
      ∫ t in (0:ℝ)..x, Real.exp (-(t^2)/2) := by
  have hi : Integrable normalDensity volume := integrable_gaussianPDFReal 0 1
  have hsub := intervalIntegral.integral_Iic_sub_Iic
    (hi.integrableOn : IntegrableOn normalDensity (Iic (0:ℝ)) volume)
    (hi.integrableOn : IntegrableOn normalDensity (Iic x) volume)
  rw [← native_power_correction_cdf_integral x,
    ← native_power_correction_cdf_integral 0] at hsub
  have hz : normalCDF 0 = 1/2 := by
    simpa only [normalCDF, cdf_eq_real] using
      AronowAudit.P053.NormalCompletion.normal_cdf_zero
  rw [hz] at hsub
  have hd : (∫ t in (0:ℝ)..x, normalDensity t) =
      (1 / Real.sqrt (2*Real.pi)) * ∫ t in (0:ℝ)..x, Real.exp (-(t^2)/2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    simp [normalDensity, gaussianPDFReal]
  linarith

/-- Rational lower and upper central-series bounds, reflected for negative endpoints. -/
def cdfLower (q : ℚ) (n : ℕ) : ℚ :=
  if 0 ≤ q then 1/2 + (39894228040143267793/10^20) *
    (gaussianIntegralInterval q n).lo
  else 1 - (1/2 + (39894228040143267795/10^20) *
    (gaussianIntegralInterval (-q) n).hi)

def cdfUpper (q : ℚ) (n : ℕ) : ℚ :=
  if 0 ≤ q then 1/2 + (39894228040143267795/10^20) *
    (gaussianIntegralInterval q n).hi
  else 1 - (1/2 + (39894228040143267793/10^20) *
    (gaussianIntegralInterval (-q) n).lo)

lemma cdf_bounds_nonneg (q : ℚ) (hq : 0 ≤ q) (n : ℕ)
    (hmono : q^2 ≤ 2*(n+2:ℕ)) :
    (cdfLower q n : ℝ) ≤ normalCDF q ∧ normalCDF q ≤ (cdfUpper q n : ℝ) := by
  have hi := gaussianIntegralInterval_sound q hq n hmono
  have hqR : (0:ℝ) ≤ q := by exact_mod_cast hq
  have hI : 0 ≤ ∫ t in (0:ℝ)..(q:ℝ), Real.exp (-(t^2)/2) :=
    intervalIntegral.integral_nonneg hqR (fun t ht => (Real.exp_pos _).le)
  rw [cdf_integral]
  simp only [cdfLower, cdfUpper, if_pos hq, Rat.cast_add, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_pow]
  constructor
  · have h₁ := mul_le_mul_of_nonneg_left hi.1
      (show (0:ℝ) ≤ 39894228040143267793/10^20 by norm_num)
    have h₂ := mul_le_mul_of_nonneg_right density_scale_bounds.1 hI
    linarith
  · have h₁ := mul_le_mul_of_nonneg_right density_scale_bounds.2 hI
    have h₂ := mul_le_mul_of_nonneg_left hi.2
      (show (0:ℝ) ≤ 39894228040143267795/10^20 by norm_num)
    linarith

lemma cdf_bounds (q : ℚ) (n : ℕ) (hmono : q^2 ≤ 2*(n+2:ℕ)) :
    (cdfLower q n : ℝ) ≤ normalCDF q ∧ normalCDF q ≤ (cdfUpper q n : ℝ) := by
  by_cases hq : 0 ≤ q
  · exact cdf_bounds_nonneg q hq n hmono
  · have hqn : 0 ≤ -q := by linarith
    have hm : (-q)^2 ≤ 2*(n+2:ℕ) := by nlinarith
    have hi := cdf_bounds_nonneg (-q) hqn n hm
    have hs : normalCDF (q:ℝ) = 1 - normalCDF ((-q:ℚ):ℝ) := by
      simpa using native_power_correction_cdf_neg (-(q:ℝ))
    rw [hs]
    simp only [cdfLower, cdfUpper, if_neg hq, Rat.cast_sub, Rat.cast_one,
      Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_pow,
      if_pos hqn] at hi ⊢
    constructor <;> linarith

/-- Every finite computation in this certificate is a rational proposition. -/
lemma cdf_certificate (q l u : ℚ) (n : ℕ)
    (hmono : q^2 ≤ 2*(n+2:ℕ))
    (hl : l ≤ cdfLower q n) (hu : cdfUpper q n ≤ u) :
    (l:ℝ) ≤ normalCDF q ∧ normalCDF q ≤ (u:ℝ) := by
  have h := cdf_bounds q n hmono
  exact ⟨le_trans (by exact_mod_cast hl) h.1, le_trans h.2 (by exact_mod_cast hu)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma z_lo_cdf : normalCDF (195996398454005/10^14) < 39/40 := by
  have h := cdf_certificate (195996398454005/10^14)
    (9749999999999997/10^16) (9749999999999999/10^16) 40
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial,
      gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ]) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial,
      gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  norm_num at h
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma z_hi_cdf : 39/40 < normalCDF (195996398454006/10^14) := by
  have h := cdf_certificate (195996398454006/10^14)
    (9750000000000001/10^16) (9750000000000005/10^16) 40
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial,
      gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ]) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial,
      gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  norm_num at h
  linarith

lemma cdf_mono : Monotone normalCDF := by
  intro x y h
  simpa only [normalCDF, cdf_eq_real] using
    AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.monotone h

lemma critical_bounds :
    (195996398454005/10^14 : ℝ) < normalCritical ∧
    normalCritical < (195996398454006/10^14 : ℝ) := by
  have hm : StrictMono normalCDF := by
    intro x y h
    simpa only [normalCDF, cdf_eq_real] using
      AronowAudit.P053.NormalCompletion.strictMono_normal_cdf h
  constructor
  · apply hm.lt_iff_lt.mp
    rw [native_power_correction_critical_cdf]
    exact z_lo_cdf
  · apply hm.lt_iff_lt.mp
    rw [native_power_correction_critical_cdf]
    exact z_hi_cdf

lemma power_upper (a : ℝ) (q r l u : ℚ)
    (hq : a-normalCritical ≤ (q:ℝ)) (hr : -a-normalCritical ≤ (r:ℝ))
    (hl : normalCDF q ≤ (l:ℝ)) (hu : normalCDF r ≤ (u:ℝ)) :
    normalPower a ≤ ((l+u:ℚ):ℝ) := by
  have h1 := (cdf_mono hq).trans hl
  have h2 := (cdf_mono hr).trans hu
  simpa only [normalPower, Rat.cast_add] using add_le_add h1 h2

lemma power_lower (a : ℝ) (q r l u : ℚ)
    (hq : (q:ℝ) ≤ a-normalCritical) (hr : (r:ℝ) ≤ -a-normalCritical)
    (hl : (l:ℝ) ≤ normalCDF q) (hu : (u:ℝ) ≤ normalCDF r) :
    ((l+u:ℚ):ℝ) ≤ normalPower a := by
  have h1 := hl.trans (cdf_mono hq)
  have h2 := hu.trans (cdf_mono hr)
  simpa only [normalPower, Rat.cast_add] using add_le_add h1 h2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma population_lower : (8972619/10000000 : ℝ) < normalPower (1/(20*binaryStudySE)) := by
  have h1 := cdf_certificate (1266102491599/1000000000000) (8972618046500687/10000000000000000) (560788627906293/625000000000000) 40
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h2 := cdf_certificate (-129650761517/25000000000) (1074118439/10000000000000000) (26852961/250000000000000) 80
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have hp := power_lower (1/(20*binaryStudySE)) (1266102491599/1000000000000) (-129650761517/25000000000)
    (8972618046500687/10000000000000000) (1074118439/10000000000000000)
    (by norm_num [binaryStudySE]; linarith [critical_bounds.2])
    (by norm_num [binaryStudySE]; linarith [critical_bounds.2]) h1.1 h2.1
  norm_num [binaryStudySE] at hp ⊢
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma population_upper : normalPower (1/(20*binaryStudySE)) < (448631/500000 : ℝ) := by
  have h1 := cdf_certificate (3165256229/2500000000) (2243154511625619/2500000000000000) (8972618046502477/10000000000000000) 40
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h2 := cdf_certificate (-5186030460679/1000000000000) (1074118439/10000000000000000) (26852961/250000000000000) 80
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have hp := power_upper (1/(20*binaryStudySE)) (3165256229/2500000000) (-5186030460679/1000000000000)
    (8972618046502477/10000000000000000) (26852961/250000000000000)
    (by norm_num [binaryStudySE]; linarith [critical_bounds.1])
    (by norm_num [binaryStudySE]; linarith [critical_bounds.1]) h1.2 h2.2
  norm_num [binaryStudySE] at hp ⊢
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root60_lo : normalPower ((1/10)*(686059/2000000)/binaryStudySE) < (3/5 : ℝ) := by
  have h1 := cdf_certificate (126653978007/500000000000) (5999848757267889/10000000000000000) (599984875726789/1000000000000000) 40
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h2 := cdf_certificate (-4173235925093/1000000000000) (75075922137/5000000000000000) (6006073771/400000000000000) 80
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have hp := power_upper ((1/10)*(686059/2000000)/binaryStudySE) (126653978007/500000000000) (-4173235925093/1000000000000)
    (599984875726789/1000000000000000) (6006073771/400000000000000)
    (by norm_num [binaryStudySE]; linarith [critical_bounds.1])
    (by norm_num [binaryStudySE]; linarith [critical_bounds.1]) h1.2 h2.2
  norm_num [binaryStudySE] at hp ⊢
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root60_hi : (3/5 : ℝ) < normalPower ((1/10)*(428787/1250000)/binaryStudySE) := by
  have h1 := cdf_certificate (126654300613/500000000000) (5999851250020793/10000000000000000) (2999925625010397/5000000000000000) 40
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h2 := cdf_certificate (-4173236570307/1000000000000) (150151418873/10000000000000000) (75075709437/5000000000000000) 80
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have hp := power_lower ((1/10)*(428787/1250000)/binaryStudySE) (126654300613/500000000000) (-4173236570307/1000000000000)
    (5999851250020793/10000000000000000) (150151418873/10000000000000000)
    (by norm_num [binaryStudySE]; linarith [critical_bounds.2])
    (by norm_num [binaryStudySE]; linarith [critical_bounds.2]) h1.1 h2.1
  norm_num [binaryStudySE] at hp ⊢
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root80_lo : normalPower ((1/10)*(4342101/10000000)/binaryStudySE) < (4/5 : ℝ) := by
  have h1 := cdf_certificate (841617309883/1000000000000) (7999989015144227/10000000000000000) (1999997253786057/2500000000000000) 40
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h2 := cdf_certificate (-2380772639481/500000000000) (4802904531/5000000000000000) (9605809063/10000000000000000) 80
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have hp := power_upper ((1/10)*(4342101/10000000)/binaryStudySE) (841617309883/1000000000000) (-2380772639481/500000000000)
    (1999997253786057/2500000000000000) (9605809063/10000000000000000)
    (by norm_num [binaryStudySE]; linarith [critical_bounds.1])
    (by norm_num [binaryStudySE]; linarith [critical_bounds.1]) h1.2 h2.2
  norm_num [binaryStudySE] at hp ⊢
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root80_hi : (4/5 : ℝ) < normalPower ((1/10)*(2171051/5000000)/binaryStudySE) := by
  have h1 := cdf_certificate (168323591019/200000000000) (999998852687201/1250000000000000) (7999990821497609/10000000000000000) 40
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h2 := cdf_certificate (-297596620261/62500000000) (1921155669/2000000000000000) (4802889173/5000000000000000) 80
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have hp := power_lower ((1/10)*(2171051/5000000)/binaryStudySE) (168323591019/200000000000) (-297596620261/62500000000)
    (999998852687201/1250000000000000) (1921155669/2000000000000000)
    (by norm_num [binaryStudySE]; linarith [critical_bounds.2])
    (by norm_num [binaryStudySE]; linarith [critical_bounds.2]) h1.1 h2.1
  norm_num [binaryStudySE] at hp ⊢
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root95_lo : normalPower ((1/10)*(698377/1250000)/binaryStudySE) < (19/20 : ℝ) := by
  have h1 := cdf_certificate (1644853019311/1000000000000) (4749999686652897/5000000000000000) (1899999874661159/2000000000000000) 40
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h2 := cdf_certificate (-556478098839/100000000000) (13124093/1000000000000000) (131240931/10000000000000000) 80
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have hp := power_upper ((1/10)*(698377/1250000)/binaryStudySE) (1644853019311/1000000000000) (-556478098839/100000000000)
    (1899999874661159/2000000000000000) (131240931/10000000000000000)
    (by norm_num [binaryStudySE]; linarith [critical_bounds.1])
    (by norm_num [binaryStudySE]; linarith [critical_bounds.1]) h1.2 h2.2
  norm_num [binaryStudySE] at hp ⊢
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root95_hi : (19/20 : ℝ) < normalPower ((1/10)*(5587017/10000000)/binaryStudySE) := by
  have h1 := cdf_certificate (1644853664523/1000000000000) (4750000019374817/5000000000000000) (1900000007749927/2000000000000000) 40
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h2 := cdf_certificate (-1112956326721/200000000000) (32810111/2500000000000000) (26248089/2000000000000000) 80
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have hp := power_lower ((1/10)*(5587017/10000000)/binaryStudySE) (1644853664523/1000000000000) (-1112956326721/200000000000)
    (4750000019374817/5000000000000000) (32810111/2500000000000000)
    (by norm_num [binaryStudySE]; linarith [critical_bounds.2])
    (by norm_num [binaryStudySE]; linarith [critical_bounds.2]) h1.1 h2.1
  norm_num [binaryStudySE] at hp ⊢
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sample_power_upper : normalPower ((1/10)*(500007878917/10^12)/binaryStudySE) < (8972711/10000000 : ℝ) := by
  have h1 := cdf_certificate (63307666371/50000000000) (8972709032702093/10000000000000000) (4486354516351047/5000000000000000) 40
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h2 := cdf_certificate (-5186081296499/1000000000000) (6711409/62500000000000) (1073825441/10000000000000000) 80
    (by norm_num) (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [cdfLower, cdfUpper, gaussianIntegralInterval, gaussianIntegralPartial, gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have hp := power_upper ((1/10)*(500007878917/10^12)/binaryStudySE) (63307666371/50000000000) (-5186081296499/1000000000000)
    (4486354516351047/5000000000000000) (1073825441/10000000000000000)
    (by norm_num [binaryStudySE]; linarith [critical_bounds.1])
    (by norm_num [binaryStudySE]; linarith [critical_bounds.1]) h1.2 h2.2
  norm_num [binaryStudySE] at hp ⊢
  linarith

lemma se_pos : 0 < binaryStudySE := by norm_num [binaryStudySE]

lemma power_strict_upper (a : ℝ) (ha : 0 < a) :
    normalPower a < normalCDF (a-normalCritical)+1/40 := by
  have hm : StrictMono normalCDF := by
    intro x y h
    simpa only [normalCDF, cdf_eq_real] using
      AronowAudit.P053.NormalCompletion.strictMono_normal_cdf h
  have ht := hm (show -a-normalCritical < -normalCritical by linarith)
  have hz := native_power_correction_cdf_neg normalCritical
  rw [native_power_correction_critical_cdf] at hz
  unfold normalPower
  linarith

lemma population_power (τ : ℝ) (hτ : |τ| ≤ 1/20) :
    normalPower (|τ|/binaryStudySE) ≤ normalPower (1/(20*binaryStudySE)) ∧
    normalPower (|τ|/binaryStudySE) < 19/20 := by
  have hs := se_pos
  have harg : |τ|/binaryStudySE ≤ 1/(20*binaryStudySE) := by
    have h := div_le_div_of_nonneg_right hτ hs.le
    convert h using 1 <;> ring
  have hpow := native_power_correction_strictMono.monotoneOn
    (div_nonneg (abs_nonneg τ) hs.le)
    (show 0 ≤ 1/(20*binaryStudySE) by positivity) harg
  exact ⟨hpow, hpow.trans_lt (population_upper.trans (by norm_num))⟩

lemma power_continuous : Continuous normalPower :=
  continuous_iff_continuousAt.mpr
    (fun a => (native_power_correction_power_deriv a).continuousAt)

lemma root_exists (l u y : ℝ) (hlu : l < u)
    (hl : normalPower ((1/10)*l/binaryStudySE) < y)
    (hu : y < normalPower ((1/10)*u/binaryStudySE)) :
    ∃ x : ℝ, l < x ∧ x < u ∧ normalPower ((1/10)*x/binaryStudySE) = y := by
  have hc : Continuous (fun x : ℝ => normalPower ((1/10)*x/binaryStudySE)) := by
    exact power_continuous.comp (by fun_prop)
  obtain ⟨x, hx, heq⟩ := intermediate_value_Icc hlu.le hc.continuousOn ⟨hl.le, hu.le⟩
  refine ⟨x, ?_, ?_, heq⟩
  · by_contra hn
    have hxl : x = l := le_antisymm (le_of_not_gt hn) hx.1
    rw [hxl] at heq
    linarith
  · by_contra hn
    have hxu : x = u := le_antisymm hx.2 (le_of_not_gt hn)
    rw [hxu] at heq
    linarith

lemma roots : ∃ σ60 σ80 σ95 : ℝ,
    normalPower ((1/10)*σ60/binaryStudySE) = 3/5 ∧
    normalPower ((1/10)*σ80/binaryStudySE) = 4/5 ∧
    normalPower ((1/10)*σ95/binaryStudySE) = 19/20 ∧
    (3430295/10^7:ℝ) < σ60 ∧ σ60 < 3430296/10^7 ∧
    (4342101/10^7:ℝ) < σ80 ∧ σ80 < 4342102/10^7 ∧
    (5587016/10^7:ℝ) < σ95 ∧ σ95 < 5587017/10^7 ∧ (1/2:ℝ) < σ95 := by
  obtain ⟨a, ha, ha', hpa⟩ := root_exists (3430295/10^7) (3430296/10^7) (3/5)
    (by norm_num) (by have h := root60_lo; norm_num at h ⊢; exact h) (by have h := root60_hi; norm_num at h ⊢; exact h)
  obtain ⟨b, hb, hb', hpb⟩ := root_exists (4342101/10^7) (4342102/10^7) (4/5)
    (by norm_num) (by have h := root80_lo; norm_num at h ⊢; exact h) (by have h := root80_hi; norm_num at h ⊢; exact h)
  obtain ⟨c, hc, hc', hpc⟩ := root_exists (5587016/10^7) (5587017/10^7) (19/20)
    (by norm_num) (by have h := root95_lo; norm_num at h ⊢; exact h) (by have h := root95_hi; norm_num at h ⊢; exact h)
  exact ⟨a, b, c, hpa, hpb, hpc, ha, ha', hb, hb', hc, hc', by linarith⟩

lemma sample_sd_ceiling (N : ℕ) (hN : 31731 ≤ N) :
    (1/2:ℝ)*Real.sqrt ((N:ℝ)/((N:ℝ)-1)) ≤ 500007878917/10^12 := by
  have hn : (31731:ℝ) ≤ N := by exact_mod_cast hN
  have hd : 0 < (N:ℝ)-1 := by linarith
  have hr : (N:ℝ)/((N:ℝ)-1) ≤ 31731/31730 := by
    apply (div_le_iff₀ hd).2
    nlinarith
  have hs : Real.sqrt ((N:ℝ)/((N:ℝ)-1)) ≤ 2*(500007878917/10^12) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · exact hr.trans (by norm_num)
  linarith

lemma sample_ceiling (N : ℕ) (hN : 31731 ≤ N) :
    (1/2:ℝ)*Real.sqrt ((N:ℝ)/((N:ℝ)-1)) ≤ 5000079/10^7 ∧
    normalPower ((1/20)*Real.sqrt ((N:ℝ)/((N:ℝ)-1))/binaryStudySE) ≤ 8972711/10^7 ∧
    normalPower ((1/20)*Real.sqrt ((N:ℝ)/((N:ℝ)-1))/binaryStudySE) < 19/20 := by
  have hs := se_pos
  have hsd := sample_sd_ceiling N hN
  have harg : (1/20)*Real.sqrt ((N:ℝ)/((N:ℝ)-1))/binaryStudySE ≤
      (1/10)*(500007878917/10^12)/binaryStudySE := by
    apply div_le_div_of_nonneg_right _ hs.le
    linarith
  have hp := native_power_correction_strictMono.monotoneOn
    (show 0 ≤ (1/20)*Real.sqrt ((N:ℝ)/((N:ℝ)-1))/binaryStudySE by positivity)
    (show 0 ≤ (1/10)*(500007878917/10^12)/binaryStudySE by positivity) harg
  have hp' := hp.trans_lt sample_power_upper
  refine ⟨hsd.trans (by norm_num), by simpa only [show (10:ℝ)^7 = 10000000 by norm_num] using hp'.le, hp'.trans (by norm_num)⟩

end binary_standardization

theorem binary_standardization_correction_proof :
    (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Y : Ω → ℝ) (p : ℝ), Measurable Y →
      (∀ᵐ ω ∂μ, Y ω = 0 ∨ Y ω = 1) → μ.real {ω | Y ω = 1} = p →
      variance Y μ = p*(1-p) ∧ variance Y μ = 1/4-(p-1/2)^2 ∧
      variance Y μ ≤ 1/4 ∧ Real.sqrt (variance Y μ) ≤ 1/2) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ Y : Fin N → ℝ,
      (∀ i, Y i = 0 ∨ Y i = 1) →
      sampleVariance Y = (N:ℝ)/((N:ℝ)-1)*sampleMean Y*(1-sampleMean Y) ∧
      sampleVariance Y ≤ (N:ℝ)/(4*((N:ℝ)-1)) ∧
      (1/10:ℝ)*sampleSD Y ≤ (1/20:ℝ)*Real.sqrt ((N:ℝ)/((N:ℝ)-1))) ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      (1/10:ℝ)*Real.sqrt (binaryPopulationVariance p) ≤ 1/20) ∧
    (∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 → |p-q| ≤ 1) ∧
    (1:ℝ) < 1229/500 ∧ normalPower 0 = 1/20 ∧
    (∀ a : ℝ, 0 < a → HasDerivAt normalPower
      (normalDensity (a-normalCritical)-normalDensity (a+normalCritical)) a ∧
      0 < normalDensity (a-normalCritical)-normalDensity (a+normalCritical) ∧
      normalPower a < normalCDF (a-normalCritical)+1/40) ∧
    StrictMonoOn normalPower (Ici 0) ∧
    (∀ τ : ℝ, |τ| ≤ 1/20 → normalPower (|τ|/binaryStudySE) ≤
      normalPower (1/(20*binaryStudySE)) ∧ normalPower (|τ|/binaryStudySE) < 19/20) ∧
    ((8972619/10^7 : ℝ) < normalPower (1/(20*binaryStudySE)) ∧
      normalPower (1/(20*binaryStudySE)) < (8972620/10^7 : ℝ)) ∧
    (∃ σ60 σ80 σ95 : ℝ,
      normalPower ((1/10)*σ60/binaryStudySE) = 3/5 ∧
      normalPower ((1/10)*σ80/binaryStudySE) = 4/5 ∧
      normalPower ((1/10)*σ95/binaryStudySE) = 19/20 ∧
      (3430295/10^7:ℝ) < σ60 ∧ σ60 < 3430296/10^7 ∧
      (4342101/10^7:ℝ) < σ80 ∧ σ80 < 4342102/10^7 ∧
      (5587016/10^7:ℝ) < σ95 ∧ σ95 < 5587017/10^7 ∧ (1/2:ℝ) < σ95) ∧
    (∀ N : ℕ, 31731 ≤ N →
      (1/2:ℝ)*Real.sqrt ((N:ℝ)/((N:ℝ)-1)) ≤ 5000079/10^7 ∧
      normalPower ((1/20)*Real.sqrt ((N:ℝ)/((N:ℝ)-1))/binaryStudySE) ≤ 8972711/10^7 ∧
      normalPower ((1/20)*Real.sqrt ((N:ℝ)/((N:ℝ)-1))/binaryStudySE) < 19/20) ∧
    (((15/4 : ℝ)-1)/36 = 11/144) ∧ (((11/4 : ℝ)-1)/10 = 7/40) ∧
    (∀ β se σ : ℝ, 0 < σ → 0 < se → (|β|/σ)/(se/σ) = |β|/se) := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num, native_power_correction_power_zero,
    ?_, native_power_correction_strictMono, binary_standardization.population_power,
    (by have hl := binary_standardization.population_lower;
        have hu := binary_standardization.population_upper;
        norm_num at hl hu ⊢; exact ⟨hl, hu⟩),
    binary_standardization.roots, binary_standardization.sample_ceiling,
    binary_table_arithmetic.2.1, binary_table_arithmetic.2.2, ?_⟩
  · intro Ω _ μ _ Y p hY hy hp
    exact binary_probability_variance μ Y p hY hy hp
  · intro N hN Y hY
    exact binary_sample_bound hN Y hY
  · intro p hp0 hp1
    have h := (binary_variance_bound p hp0 hp1).2.2.2
    linarith
  · intro p q hp0 hp1 hq0 hq1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro a ha
    exact ⟨native_power_correction_power_deriv a,
      native_power_correction_deriv_pos a ha, binary_standardization.power_strict_upper a ha⟩
  · intro β se σ hσ hse
    exact standardized_ratio |β| se σ hσ.ne' hse.ne'


namespace caliper_counterexample

local instance instDecidableCaliperCounterexample (p : Prop) : Decidable p := Classical.propDecidable p

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def active (W : Set ℝ) (X : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => X i ∈ W)

def pattern (W U : Set ℝ) (S T : Finset ι) : Set (ι → ℝ) :=
  Set.univ.pi (fun i => if i ∈ T then U else if i ∈ S then W \ U else Wᶜ)

lemma pattern_iff {W U : Set ℝ} (hUW : U ⊆ W) (S T : Finset ι) (hTS : T ⊆ S)
    (X : ι → ℝ) :
    X ∈ pattern W U S T ↔ active W X = S ∧ active U X = T := by
  simp only [pattern, Set.mem_univ_pi]
  constructor
  · intro h
    constructor
    · ext i
      specialize h i
      by_cases ht : i ∈ T
      · have hs := hTS ht
        simp only [if_pos ht] at h
        simp [active, hs, hUW h]
      · by_cases hs : i ∈ S
        · simp only [if_neg ht, if_pos hs] at h
          simp [active, hs, h.1]
        · simp only [if_neg ht, if_neg hs, Set.mem_compl_iff] at h
          simp [active, hs, h]
    · ext i
      specialize h i
      by_cases ht : i ∈ T
      · simp only [if_pos ht] at h
        simp [active, ht, h]
      · by_cases hs : i ∈ S
        · simp only [if_neg ht, if_pos hs] at h
          simp [active, ht, h.2]
        · simp only [if_neg ht, if_neg hs, Set.mem_compl_iff] at h
          have hu : X i ∉ U := fun hi => h (hUW hi)
          simp [active, ht, hu]
  · rintro ⟨hW, hU⟩ i
    have hw : X i ∈ W ↔ i ∈ S := by
      rw [← hW]
      simp [active]
    have hu : X i ∈ U ↔ i ∈ T := by
      rw [← hU]
      simp [active]
    split_ifs with ht hs
    · exact hu.mpr ht
    · exact ⟨hw.mpr hs, fun hi => ht (hu.mp hi)⟩
    · exact fun hi => hs (hw.mp hi)

lemma pattern_measurable {W U : Set ℝ} (hW : MeasurableSet W) (hU : MeasurableSet U)
    (S T : Finset ι) : MeasurableSet (pattern W U S T) := by
  apply MeasurableSet.univ_pi
  intro i
  split_ifs
  · exact hU
  · exact hW.diff hU
  · exact hW.compl

lemma pattern_measure (ν : Measure ℝ) [IsFiniteMeasure ν] (W U : Set ℝ)
    (S T : Finset ι) (hTS : T ⊆ S) :
    (Measure.pi (fun _ : ι => ν)).real (pattern W U S T) =
      ν.real U ^ T.card * ν.real (W \ U) ^ (S.card-T.card) *
        ν.real Wᶜ ^ (Fintype.card ι-S.card) := by
  rw [measureReal_def, pattern, Measure.pi_pi, ENNReal.toReal_prod]
  have hprod : (∏ i : ι, (ν (if i ∈ T then U else if i ∈ S then W \ U else Wᶜ)).toReal) =
      ∏ i : ι, if i ∈ T then ν.real U else if i ∈ S then ν.real (W \ U) else ν.real Wᶜ := by
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> rfl
  rw [hprod, Finset.prod_ite]
  have h1 : Finset.univ.filter (fun i => i ∈ T) = T := by ext i; simp
  have h2 : Finset.univ.filter (fun i => i ∉ T) = Finset.univ \ T := by ext i; simp
  rw [h1, h2, Finset.prod_const, Finset.prod_ite]
  have h3 : (Finset.univ \ T).filter (fun i => i ∈ S) = S \ T := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  have h4 : (Finset.univ \ T).filter (fun i => i ∉ S) = Finset.univ \ S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · exact And.right
    · intro hi
      exact ⟨fun ht => hi (hTS ht), hi⟩
  rw [h3, h4, Finset.prod_const, Finset.prod_const,
    Finset.card_sdiff_of_subset hTS,
    Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
  ring

lemma active_pattern (W : Set ℝ) (S : Finset ι) :
    {X : ι → ℝ | active W X = S} =
      Set.univ.pi (fun i => if i ∈ S then W else Wᶜ) := by
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_univ_pi]
  constructor
  · intro h i
    have hi : X i ∈ W ↔ i ∈ S := by rw [← h]; simp [active]
    split_ifs with hs
    · exact hi.mpr hs
    · exact fun hx => hs (hi.mp hx)
  · intro h
    ext i
    specialize h i
    by_cases hs : i ∈ S <;> simp_all [active]

lemma active_measurable {W : Set ℝ} (hW : MeasurableSet W) (S : Finset ι) :
    MeasurableSet {X : ι → ℝ | active W X = S} := by
  rw [active_pattern]
  apply MeasurableSet.univ_pi
  intro i
  split_ifs
  · exact hW
  · exact hW.compl

lemma active_measure (ν : Measure ℝ) [IsFiniteMeasure ν] (W : Set ℝ) (S : Finset ι) :
    (Measure.pi (fun _ : ι => ν)).real {X | active W X = S} =
      ν.real W ^ S.card * ν.real Wᶜ ^ (Fintype.card ι-S.card) := by
  rw [active_pattern, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  simp only [apply_ite, measureReal_def]
  rw [Finset.prod_ite]
  have h1 : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
  have h2 : Finset.univ.filter (fun i => i ∉ S) = Finset.univ \ S := by ext i; simp
  rw [h1, h2, Finset.prod_const, Finset.prod_const,
    Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]

lemma success_subset {W U : Set ℝ} (hUW : U ⊆ W) (X : ι → ℝ) :
    active U X ⊆ active W X := by
  intro i hi
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hUW hi

lemma tail_union {W U : Set ℝ} (hUW : U ⊆ W) (S : Finset ι) (k : ℕ) :
    {X : ι → ℝ | active W X = S ∧ k ≤ (active U X).card} =
      ⋃ T ∈ S.powerset.filter (fun T => k ≤ T.card), pattern W U S T := by
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hS, hk⟩
    have hT : active U X ⊆ S := by simpa only [hS] using success_subset hUW X
    refine ⟨active U X, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT, hk⟩, ?_⟩
    exact (pattern_iff hUW S (active U X) hT X).mpr ⟨hS, rfl⟩
  · rintro ⟨T, hT, hX⟩
    have ht := Finset.mem_filter.mp hT
    have hx := (pattern_iff hUW S T (Finset.mem_powerset.mp ht.1) X).mp hX
    exact ⟨hx.1, by simpa only [hx.2] using ht.2⟩

lemma pattern_disjoint {W U : Set ℝ} (hUW : U ⊆ W) (S : Finset ι) (k : ℕ) :
    Set.PairwiseDisjoint (↑(S.powerset.filter (fun T => k ≤ T.card))) (pattern W U S) := by
  intro T hT T' hT' hne
  apply Set.disjoint_left.mpr
  intro X hX hX'
  have ht := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  have ht' := Finset.mem_powerset.mp (Finset.mem_filter.mp hT').1
  have hx := (pattern_iff hUW S T ht X).mp hX
  have hx' := (pattern_iff hUW S T' ht' X).mp hX'
  exact hne (hx.2.symm.trans hx'.2)

lemma subset_sum (S : Finset ι) (k : ℕ) (A B C : ℝ) :
    (∑ T ∈ S.powerset.filter (fun T => k ≤ T.card),
      A^T.card * B^(S.card-T.card) * C) =
      (∑ j ∈ Finset.Icc k S.card, (S.card.choose j:ℝ)*A^j*B^(S.card-j))*C := by
  rw [Finset.sum_filter, Finset.sum_powerset]
  have hinner (j : ℕ) :
      (∑ T ∈ Finset.powersetCard j S, if k ≤ T.card then A^T.card*B^(S.card-T.card)*C else 0) =
      (S.card.choose j:ℝ)*(if k ≤ j then A^j*B^(S.card-j)*C else 0) := by
    have h := Finset.sum_powersetCard j S
      (fun t => if k ≤ t then A^t*B^(S.card-t)*C else 0)
    simpa only [nsmul_eq_mul, mul_comm] using h
  simp_rw [hinner, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hs : (Finset.range (S.card+1)).filter (fun j => k ≤ j) = Finset.Icc k S.card := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [hs, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma tail_factor (n k : ℕ) (A B : ℝ) (hAB : A+B ≠ 0) :
    (∑ j ∈ Finset.Icc k n, (n.choose j:ℝ)*A^j*B^(n-j)) =
      (A+B)^n * binomialTail n k (A/(A+B)) := by
  have hc : 1-A/(A+B) = B/(A+B) := by field_simp; ring
  unfold binomialTail
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
  rw [hc, div_pow, div_pow]
  have hp : (A+B)^n = (A+B)^j*(A+B)^(n-j) := by
    rw [← pow_add, Nat.add_sub_of_le hjn]
  rw [hp]
  field_simp
  <;> ring

lemma fixed_pattern_tail (ν : Measure ℝ) [IsFiniteMeasure ν]
    {W U : Set ℝ} (hW : MeasurableSet W) (hU : MeasurableSet U) (hUW : U ⊆ W)
    (hpos : 0 < ν.real W) (S : Finset ι) (k : ℕ) :
    (Measure.pi (fun _ : ι => ν)).real
      {X | active W X = S ∧ k ≤ (active U X).card} =
      (Measure.pi (fun _ : ι => ν)).real {X | active W X = S} *
        binomialTail S.card k (ν.real U / ν.real W) := by
  rw [tail_union hUW S k,
    measureReal_biUnion_finset (pattern_disjoint hUW S k)
      (fun T hT => pattern_measurable hW hU S T)]
  have hsum : (∑ T ∈ S.powerset.filter (fun T => k ≤ T.card),
      (Measure.pi (fun _ : ι => ν)).real (pattern W U S T)) =
      ∑ T ∈ S.powerset.filter (fun T => k ≤ T.card),
        ν.real U^T.card*ν.real (W \ U)^(S.card-T.card)*
          ν.real Wᶜ^(Fintype.card ι-S.card) := by
    apply Finset.sum_congr rfl
    intro T hT
    exact pattern_measure ν W U S T (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)
  rw [hsum, subset_sum, active_measure]
  have hAB : ν.real U+ν.real (W \ U) = ν.real W := by
    rw [measureReal_sdiff hUW hU]
    ring
  rw [tail_factor S.card k (ν.real U) (ν.real (W \ U)) (by rw [hAB]; exact hpos.ne')]
  rw [hAB]
  ring

lemma count_union (W : Set ℝ) (n : ℕ) :
    {X : ι → ℝ | (active W X).card = n} =
      ⋃ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => S.card = n),
        {X | active W X = S} := by
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨active W X, h, rfl⟩
  · rintro ⟨S, hS, hX⟩
    simpa only [hX] using hS

lemma count_tail_union (W U : Set ℝ) (n k : ℕ) :
    {X : ι → ℝ | (active W X).card = n ∧ k ≤ (active U X).card} =
      ⋃ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => S.card = n),
        {X | active W X = S ∧ k ≤ (active U X).card} := by
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, hk⟩
    exact ⟨active W X, h, rfl, hk⟩
  · rintro ⟨S, hS, hX, hk⟩
    exact ⟨by simpa only [hX] using hS, hk⟩

lemma conditional_tail (ν : Measure ℝ) [IsFiniteMeasure ν]
    {W U : Set ℝ} (hW : MeasurableSet W) (hU : MeasurableSet U) (hUW : U ⊆ W)
    (hpos : 0 < ν.real W) (n k : ℕ)
    (hn : 0 < (Measure.pi (fun _ : ι => ν)).real {X | (active W X).card = n}) :
    (Measure.pi (fun _ : ι => ν)).real
      {X | (active W X).card = n ∧ k ≤ (active U X).card} /
      (Measure.pi (fun _ : ι => ν)).real {X | (active W X).card = n} =
      binomialTail n k (ν.real U / ν.real W) := by
  let F : Finset (Finset ι) := Finset.univ.filter (fun S => S.card = n)
  have hd : Set.PairwiseDisjoint (↑F) (fun S => {X : ι → ℝ | active W X = S}) := by
    intro S hS T hT hne
    apply Set.disjoint_left.mpr
    intro X hX hX'
    exact hne (hX.symm.trans hX')
  have hd' : Set.PairwiseDisjoint (↑F)
      (fun S => {X : ι → ℝ | active W X = S ∧ k ≤ (active U X).card}) := by
    intro S hS T hT hne
    apply Set.disjoint_left.mpr
    intro X hX hX'
    exact hne (hX.1.symm.trans hX'.1)
  have hm (S : Finset ι) :
      MeasurableSet {X : ι → ℝ | active W X = S ∧ k ≤ (active U X).card} := by
    rw [tail_union hUW S k]
    exact MeasurableSet.biUnion (to_countable _) (fun T hT => pattern_measurable hW hU S T)
  apply (div_eq_iff hn.ne').2
  rw [count_tail_union, count_union,
    measureReal_biUnion_finset hd' (fun S hS => hm S),
    measureReal_biUnion_finset hd (fun S hS => active_measurable hW S), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hs : S.card = n := (Finset.mem_filter.mp hS).2
  rw [fixed_pattern_tail ν hW hU hUW hpos S k, hs]
  ring

lemma linear_nonneg (x : ℝ) : 0 ≤ linearCaliperDensity x := by
  unfold linearCaliperDensity
  split_ifs with hx
  · exact div_nonneg hx.1 (by norm_num)
  · rfl

lemma linear_integrable : Integrable linearCaliperDensity volume := by
  have he : linearCaliperDensity = (Icc (0:ℝ) 4).indicator (fun x => x/8) := by
    funext x
    simp only [linearCaliperDensity, Set.indicator_apply]
  rw [he, integrable_indicator_iff measurableSet_Icc]
  exact (continuous_id.div_const 8).integrableOn_Icc

lemma density_interval (f : ℝ → ℝ) (hf : Integrable f volume) (hfn : ∀ x, 0 ≤ f x)
    (a b : ℝ) (hab : a ≤ b) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).real (Icc a b) =
      ∫ x in a..b, f x := by
  rw [measureReal_def, withDensity_apply _ measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn
      (Filter.Eventually.of_forall hfn), ENNReal.toReal_ofReal
      (setIntegral_nonneg measurableSet_Icc (fun x hx => hfn x)),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

lemma linear_density_finite : IsFiniteMeasure
    (volume.withDensity (fun x => ENNReal.ofReal (linearCaliperDensity x))) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal linear_integrable
    (Filter.Eventually.of_forall linear_nonneg)]
  exact ENNReal.ofReal_ne_top

lemma linear_conditional_tail (M : ℕ)
    (hn : 0 < (caliperDataLaw M linearCaliperDensity).real
      {X | caliperCount (caliperCutoff/5) X = 19}) :
    (caliperDataLaw M linearCaliperDensity).real
      ({X | caliperCount (caliperCutoff/5) X = 19} ∩
        {X | 14 ≤ caliperSuccesses (caliperCutoff/5) X}) /
      (caliperDataLaw M linearCaliperDensity).real
        {X | caliperCount (caliperCutoff/5) X = 19} = binomialTail 19 14 (11/20) := by
  let ν := volume.withDensity (fun x => ENNReal.ofReal (linearCaliperDensity x))
  letI instFiniteLinear : IsFiniteMeasure ν := linear_density_finite
  let W := Icc (caliperCutoff-caliperCutoff/5) (caliperCutoff+caliperCutoff/5)
  let U := Icc caliperCutoff (caliperCutoff+caliperCutoff/5)
  have hUW : U ⊆ W := by
    intro x hx
    exact ⟨by dsimp [W, U, caliperCutoff] at *; linarith [hx.1], hx.2⟩
  have hU : ν.real U = 26411/250000 := by
    dsimp [ν, U]
    rw [density_interval linearCaliperDensity linear_integrable linear_nonneg _ _
      (by norm_num [caliperCutoff])]
    exact (linear_caliper_witness).2.2.2.2.1
  have hW : ν.real W = 2401/12500 := by
    dsimp [ν, W]
    rw [density_interval linearCaliperDensity linear_integrable linear_nonneg _ _
      (by norm_num [caliperCutoff])]
    have hi := intervalIntegral.integral_add_adjacent_intervals
      linear_integrable.intervalIntegrable linear_integrable.intervalIntegrable
      (a := caliperCutoff-caliperCutoff/5) (b := caliperCutoff)
      (c := caliperCutoff+caliperCutoff/5)
    change caliperBelow linearCaliperDensity (caliperCutoff/5) +
      caliperAbove linearCaliperDensity (caliperCutoff/5) = _ at hi
    rw [(linear_caliper_witness).2.2.2.2.1, (linear_caliper_witness).2.2.2.2.2.1] at hi
    linarith
  have hratio : ν.real U / ν.real W = 11/20 := by rw [hU, hW]; norm_num
  have hcount (X : Fin M → ℝ) : (active W X).card = caliperCount (caliperCutoff/5) X := by
    unfold active caliperCount
    congr 1
    ext i
    simp only [Finset.mem_filter, W]
  have hsuccess (X : Fin M → ℝ) : (active U X).card = caliperSuccesses (caliperCutoff/5) X := by
    unfold active caliperSuccesses
    congr 1
    ext i
    simp only [Finset.mem_filter, U]
  have h := conditional_tail (ι := Fin M) ν (W := W) (U := U)
    measurableSet_Icc measurableSet_Icc hUW (by rw [hW]; norm_num) 19 14
    (by simpa only [hcount, caliperDataLaw, ν] using hn)
  rw [hratio] at h
  simpa only [hcount, hsuccess, Set.setOf_and, caliperDataLaw, ν] using h

lemma window_bounds (h : ℝ) (hh : 0 < h) (hc : h < caliperCutoff)
    (x : ℝ) (hx : x ∈ Icc (caliperCutoff-h) (caliperCutoff+h)) : 0 < x ∧ x < 4 := by
  norm_num [caliperCutoff] at hc hx
  constructor <;> linarith [hx.1, hx.2]

lemma linear_smooth (h : ℝ) (hh : 0 < h) (hc : h < caliperCutoff) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) linearCaliperDensity
      (Ioo (caliperCutoff-h) (caliperCutoff+h)) := by
  have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => x/8) := by fun_prop
  apply hp.contDiffOn.congr
  intro x hx
  have hx' := window_bounds h hh hc x ⟨hx.1.le, hx.2.le⟩
  simp only [linearCaliperDensity, if_pos (show x ∈ Icc (0:ℝ) 4 from ⟨hx'.1.le, hx'.2.le⟩)]

lemma polynomial_integral (m : ℕ) (a b : ℝ) :
    (∫ x in a..b, ((m:ℝ)+1)*x^m/4^(m+1)) =
      (b^(m+1)-a^(m+1))/4^(m+1) := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
  have hm : (m:ℝ)+1 ≠ 0 := by positivity
  push_cast
  field_simp
  <;> ring

lemma power_masses (m : ℕ) (h : ℝ) (hh : 0 < h) (hc : h < caliperCutoff) :
    caliperAbove (powerCaliperDensity m) h =
      ((caliperCutoff+h)^(m+1)-caliperCutoff^(m+1))/4^(m+1) ∧
    caliperBelow (powerCaliperDensity m) h =
      (caliperCutoff^(m+1)-(caliperCutoff-h)^(m+1))/4^(m+1) := by
  have he (x : ℝ) (hx : x ∈ Icc (caliperCutoff-h) (caliperCutoff+h)) :
      powerCaliperDensity m x = ((m:ℝ)+1)*x^m/4^(m+1) := by
    have hx' := window_bounds h hh hc x hx
    exact if_pos ⟨hx'.1.le, hx'.2.le⟩
  constructor
  · unfold caliperAbove
    calc
      _ = ∫ x in caliperCutoff..caliperCutoff+h, ((m:ℝ)+1)*x^m/4^(m+1) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith : caliperCutoff ≤ caliperCutoff+h)] at hx
        exact he x ⟨by linarith [hx.1], hx.2⟩
      _ = _ := polynomial_integral m _ _
  · unfold caliperBelow
    calc
      _ = ∫ x in caliperCutoff-h..caliperCutoff, ((m:ℝ)+1)*x^m/4^(m+1) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith : caliperCutoff-h ≤ caliperCutoff)] at hx
        exact he x ⟨hx.1, by linarith [hx.2]⟩
      _ = _ := polynomial_integral m _ _

lemma power_formula (m : ℕ) (h : ℝ) (hh : 0 < h) (hc : h < caliperCutoff) :
    caliperProbability (powerCaliperDensity m) h =
      ((caliperCutoff+h)^(m+1)-caliperCutoff^(m+1))/
        ((caliperCutoff+h)^(m+1)-(caliperCutoff-h)^(m+1)) := by
  have hc0 : 0 < caliperCutoff := by norm_num [caliperCutoff]
  have hpos : 0 < (caliperCutoff+h)^(m+1)-(caliperCutoff-h)^(m+1) := by
    apply sub_pos.mpr
    exact pow_lt_pow_left₀ (by linarith) (by linarith) (by omega)
  unfold caliperProbability
  rw [(power_masses m h hh hc).1, (power_masses m h hh hc).2]
  have hp : (4:ℝ)^(m+1) ≠ 0 := by positivity
  rw [← add_div, show ((caliperCutoff+h)^(m+1)-caliperCutoff^(m+1)) +
    (caliperCutoff^(m+1)-(caliperCutoff-h)^(m+1)) =
    (caliperCutoff+h)^(m+1)-(caliperCutoff-h)^(m+1) by ring]
  exact div_div_div_cancel_right₀ hp _ _

lemma power_positive_smooth (m : ℕ) (h : ℝ) (hh : 0 < h) (hc : h < caliperCutoff) :
    (∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h), 0 < powerCaliperDensity m x) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (powerCaliperDensity m)
      (Ioo (caliperCutoff-h) (caliperCutoff+h)) := by
  have he (x : ℝ) (hx : x ∈ Icc (caliperCutoff-h) (caliperCutoff+h)) :
      powerCaliperDensity m x = ((m:ℝ)+1)*x^m/4^(m+1) := by
    have hx' := window_bounds h hh hc x hx
    exact if_pos ⟨hx'.1.le, hx'.2.le⟩
  constructor
  · intro x hx
    rw [he x hx]
    have hx' := (window_bounds h hh hc x hx).1
    positivity
  · have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => ((m:ℝ)+1)*x^m/4^(m+1)) := by fun_prop
    apply hp.contDiffOn.congr
    intro x hx
    exact he x ⟨hx.1.le, hx.2.le⟩

lemma power_limit (h : ℝ) (hh : 0 < h) (hc : h < caliperCutoff) :
    Tendsto (fun m : ℕ => caliperProbability (powerCaliperDensity m) h) atTop (𝓝 1) := by
  have hc0 : 0 < caliperCutoff := by norm_num [caliperCutoff]
  have hch : 0 < caliperCutoff+h := by linarith
  have ha0 : 0 ≤ caliperCutoff/(caliperCutoff+h) := by positivity
  have ha1 : caliperCutoff/(caliperCutoff+h) < 1 := (div_lt_one hch).2 (by linarith)
  have hb0 : 0 ≤ (caliperCutoff-h)/(caliperCutoff+h) := by positivity
  have hb1 : (caliperCutoff-h)/(caliperCutoff+h) < 1 := (div_lt_one hch).2 (by linarith)
  have ha := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).comp (tendsto_add_atTop_nat 1)
  have hb := (tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1).comp (tendsto_add_atTop_nat 1)
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have ht := (hone.sub ha).div (hone.sub hb)
    (show (1:ℝ)-0 ≠ 0 by norm_num)
  have he (m : ℕ) : caliperProbability (powerCaliperDensity m) h =
      (1-(caliperCutoff/(caliperCutoff+h))^(m+1)) /
        (1-((caliperCutoff-h)/(caliperCutoff+h))^(m+1)) := by
    rw [power_formula m h hh hc, div_pow, div_pow]
    have hp : (caliperCutoff+h)^(m+1) ≠ 0 := by positivity
    have hnum : 1-caliperCutoff^(m+1)/(caliperCutoff+h)^(m+1) =
        ((caliperCutoff+h)^(m+1)-caliperCutoff^(m+1))/(caliperCutoff+h)^(m+1) := by
      field_simp
    have hden : 1-(caliperCutoff-h)^(m+1)/(caliperCutoff+h)^(m+1) =
        ((caliperCutoff+h)^(m+1)-(caliperCutoff-h)^(m+1))/(caliperCutoff+h)^(m+1) := by
      field_simp
    rw [hnum, hden, div_div_div_cancel_right₀ hp]
  simp only [sub_zero, div_one] at ht
  exact ht.congr' (Eventually.of_forall (fun m => (he m).symm))

lemma tail_antitone (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Antitone (fun k => binomialTail n k p) := by
  intro k l hkl
  unfold binomialTail
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact Finset.mem_Icc.mpr ⟨hkl.trans (Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2⟩
  · intro j hj hj'
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hp0 _))
      (pow_nonneg (by linarith : 0 ≤ 1-p) _)

lemma rejection_cutoff (k : ℕ) : binomialTail 19 k (1/2) ≤ 1/20 ↔ 14 ≤ k := by
  have hmono := tail_antitone 19 (1/2) (by norm_num) (by norm_num)
  have hlo : (1/20:ℝ) < binomialTail 19 13 (1/2) := caliper_exact_tails.2.2.2.2.2.2.2.1
  have hhi : binomialTail 19 14 (1/2) < (1/20:ℝ) := caliper_exact_tails.2.2.2.2.2.2.2.2.1
  constructor
  · intro hk
    by_contra hn
    have hkle : k ≤ 13 := by omega
    have h := hmono hkle
    linarith
  · intro hk
    exact (hmono hk).trans hhi.le

lemma linear_rejection (M : ℕ)
    (hn : 0 < (caliperDataLaw M linearCaliperDensity).real
      {X | caliperCount (caliperCutoff/5) X = 19}) :
    (caliperDataLaw M linearCaliperDensity).real
      ({X | caliperCount (caliperCutoff/5) X = 19} ∩
        {X | binomialTail 19 (caliperSuccesses (caliperCutoff/5) X) (1/2) ≤ 1/20}) /
      (caliperDataLaw M linearCaliperDensity).real
        {X | caliperCount (caliperCutoff/5) X = 19} = binomialTail 19 14 (11/20) := by
  have he : {X : Fin M → ℝ | binomialTail 19 (caliperSuccesses (caliperCutoff/5) X) (1/2) ≤ 1/20} =
      {X | 14 ≤ caliperSuccesses (caliperCutoff/5) X} := by
    ext X
    exact rejection_cutoff _
  rw [he]
  exact linear_conditional_tail M hn

lemma gaussian_interval (θ a b : ℝ) (hab : a ≤ b) :
    (gaussianReal θ 1).real (Icc a b) = normalCDF (b-θ)-normalCDF (a-θ) := by
  letI instNullGaussian : NullSingletonClass (gaussianReal θ 1) :=
    nullSingletonClass_gaussianReal (by norm_num : (1:NNReal) ≠ 0)
  have hs : Iic b \ Iic a = Ioc a b := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Iic, Set.mem_Ioc, not_le]
    tauto
  have hm := measureReal_sdiff (μ := gaussianReal θ 1) (Iic_subset_Iic.mpr hab) measurableSet_Iic
  rw [hs, native_power_correction_shifted_cdf, native_power_correction_shifted_cdf] at hm
  calc
    _ = (gaussianReal θ 1).real (Ioc a b) :=
      measureReal_congr (Ioc_ae_eq_Icc' (measure_singleton a)).symm
    _ = _ := hm

/-- The location is unrestricted in both clauses; only the folded-CDF argument is nonnegative. -/
lemma folded_gaussian_formula_coverage :
    (∀ θ x : ℝ, 0 ≤ x → (gaussianReal θ 1).real {t | |t| ≤ x} = foldedNormalCDF θ x) ∧
    (∀ θ : ℝ, intervalCoverage (gaussianReal θ 1) id θ normalCritical = 19/20) := by
  constructor
  · intro θ x hx
    have he : {t : ℝ | |t| ≤ x} = Icc (-x) x := by
      ext t
      change |t| ≤ x ↔ -x ≤ t ∧ t ≤ x
      exact abs_le
    rw [he, gaussian_interval θ (-x) x (by linarith)]
    rfl
  · intro θ
    have hz := native_power_correction_critical_pos
    have he : {t : ℝ | θ ∈ Icc (id t-normalCritical) (id t+normalCritical)} =
        Icc (θ-normalCritical) (θ+normalCritical) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Icc, id_eq]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    unfold intervalCoverage
    rw [he, gaussian_interval θ _ _ (by linarith)]
    rw [show (θ+normalCritical)-θ = normalCritical by ring,
      show (θ-normalCritical)-θ = -normalCritical by ring,
      native_power_correction_cdf_neg, native_power_correction_critical_cdf]
    norm_num

lemma tail_interval (p l u : ℝ) (hl0 : 0 ≤ l) (hlp : l ≤ p) (hpu : p ≤ u) (hu1 : u ≤ 1) :
    (∑ j ∈ Finset.Icc 14 19, (Nat.choose 19 j:ℝ)*l^j*(1-u)^(19-j)) ≤ binomialTail 19 14 p ∧
    binomialTail 19 14 p ≤ ∑ j ∈ Finset.Icc 14 19, (Nat.choose 19 j:ℝ)*u^j*(1-l)^(19-j) := by
  have hp0 : 0 ≤ p := hl0.trans hlp
  have hu0 : 0 ≤ u := hp0.trans hpu
  have hp1 : p ≤ 1 := hpu.trans hu1
  have hl1 : l ≤ 1 := hlp.trans hp1
  unfold binomialTail
  constructor
  · apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 hlp _) (by positivity))
      (pow_le_pow_left₀ (by linarith : 0 ≤ 1-u) (by linarith : 1-u ≤ 1-p) _)
      (pow_nonneg (by linarith) _)
      (mul_nonneg (by positivity) (pow_nonneg hp0 _))
  · apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hpu _) (by positivity))
      (pow_le_pow_left₀ (by linarith : 0 ≤ 1-p) (by linarith : 1-p ≤ 1-l) _)
      (pow_nonneg (by linarith) _)
      (mul_nonneg (by positivity) (pow_nonneg hu0 _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma folded_shift :
    (80593469763037/125000000000000 : ℝ) ≤ foldedCaliperProbability (7/2) (49/125) ∧
    foldedCaliperProbability (7/2) (49/125) ≤ (644747758104297/1000000000000000 : ℝ) := by
  have h1 := binary_standardization.cdf_certificate (-287/250) (1254842819162958359/10000000000000000000) (31371070479073959/250000000000000000) 40
    (by norm_num) (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h2 := binary_standardization.cdf_certificate (-1463/250) (3035603927/1250000000000000000) (24284831417/10000000000000000000) 90
    (by norm_num) (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h3 := binary_standardization.cdf_certificate (-77/50) (123560353423623791/2000000000000000000) (154450441779529739/2500000000000000000) 40
    (by norm_num) (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h4 := binary_standardization.cdf_certificate (-273/50) (119033645813/5000000000000000000) (59516822907/2500000000000000000) 90
    (by norm_num) (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h5 := binary_standardization.cdf_certificate (-483/250) (266797529391301397/10000000000000000000) (133398764695650699/5000000000000000000) 40
    (by norm_num) (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h6 := binary_standardization.cdf_certificate (-1267/250) (2010087027767/10000000000000000000) (251260878471/1250000000000000000) 90
    (by norm_num) (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  norm_num at h1 h2 h3 h4 h5 h6
  have hd : 0 < foldedNormalCDF (7/2) (caliperCutoff+49/125) -
      foldedNormalCDF (7/2) (caliperCutoff-49/125) := by
    norm_num [foldedNormalCDF, caliperCutoff]
    linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
  unfold foldedCaliperProbability
  constructor
  · apply (le_div_iff₀ hd).2
    norm_num [foldedNormalCDF, caliperCutoff]
    linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
  · apply (div_le_iff₀ hd).2
    norm_num [foldedNormalCDF, caliperCutoff]
    linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma folded_zero :
    (159472249535649/500000000000000 : ℝ) ≤ foldedCaliperProbability (0/1) (49/125) ∧
    foldedCaliperProbability (0/1) (49/125) ≤ (318944499071299/1000000000000000 : ℝ) := by
  have h1 := binary_standardization.cdf_certificate (294/125) (9906636125313244183/10000000000000000000) (1238329515664155523/1250000000000000000) 60
    (by norm_num) (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h2 := binary_standardization.cdf_certificate (-294/125) (11670484335844477/1250000000000000000) (93363874686755817/10000000000000000000) 60
    (by norm_num) (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h3 := binary_standardization.cdf_certificate (49/25) (4875010524258897829/5000000000000000000) (9750021048517795659/10000000000000000000) 40
    (by norm_num) (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h4 := binary_standardization.cdf_certificate (-49/25) (249978951482204341/10000000000000000000) (124989475741102171/5000000000000000000) 40
    (by norm_num) (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h5 := binary_standardization.cdf_certificate (196/125) (4707797169128939737/5000000000000000000) (376623773530315179/400000000000000000) 40
    (by norm_num) (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  have h6 := binary_standardization.cdf_certificate (-196/125) (23376226469684821/400000000000000000) (292202830871060263/5000000000000000000) 40
    (by norm_num) (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
    (by norm_num [binary_standardization.cdfLower, binary_standardization.cdfUpper, binary_standardization.gaussianIntegralInterval, binary_standardization.gaussianIntegralPartial, binary_standardization.gaussianIntegralTerm, Finset.sum_range_succ, Nat.factorial_succ])
  norm_num at h1 h2 h3 h4 h5 h6
  have hd : 0 < foldedNormalCDF (0/1) (caliperCutoff+49/125) -
      foldedNormalCDF (0/1) (caliperCutoff-49/125) := by
    norm_num [foldedNormalCDF, caliperCutoff]
    linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
  unfold foldedCaliperProbability
  constructor
  · apply (le_div_iff₀ hd).2
    norm_num [foldedNormalCDF, caliperCutoff]
    linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
  · apply (div_le_iff₀ hd).2
    norm_num [foldedNormalCDF, caliperCutoff]
    linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

set_option maxHeartbeats 0 in
lemma folded_tail :
    (280413461677/10^12:ℝ) ≤ binomialTail 19 14 (foldedCaliperProbability (7/2) (49/125)) ∧
    binomialTail 19 14 (foldedCaliperProbability (7/2) (49/125)) ≤ 280413461678/10^12 := by
  have hp := tail_interval (foldedCaliperProbability (7/2) (49/125))
    (644747758104296/10^15) (644747758104297/10^15) (by norm_num)
    (by convert folded_shift.1 using 1 <;> norm_num)
    (by convert folded_shift.2 using 1 <;> norm_num) (by norm_num)
  have hIcc : Finset.Icc 14 19 = {14,15,16,17,18,19} := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hlo : (280413461677/10^12:ℝ) ≤
      ∑ j ∈ Finset.Icc 14 19, (Nat.choose 19 j:ℝ)*(644747758104296/10^15)^j*
        (1-644747758104297/10^15)^(19-j) := by
    norm_num [hIcc, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  have hhi : (∑ j ∈ Finset.Icc 14 19, (Nat.choose 19 j:ℝ)*(644747758104297/10^15)^j*
        (1-644747758104296/10^15)^(19-j)) ≤ (280413461678/10^12:ℝ) := by
    norm_num [hIcc, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  exact ⟨hlo.trans hp.1, hp.2.trans hhi⟩

lemma linear_windows :
    ∀ r ∈ ({(1/10:ℝ),3/20,1/5} : Finset ℝ),
      let h := caliperCutoff*r;
      0 < h ∧ h < caliperCutoff ∧
      (∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h), 0 < linearCaliperDensity x) ∧
      caliperAbove linearCaliperDensity h = (2*caliperCutoff*h+h^2)/16 ∧
      caliperBelow linearCaliperDensity h = (2*caliperCutoff*h-h^2)/16 ∧
      caliperProbability linearCaliperDensity h = 1/2+r/4 ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) linearCaliperDensity
        (Ioo (caliperCutoff-h) (caliperCutoff+h)) := by
  intro r hr
  dsimp only
  have hr' : 0 < r ∧ r < 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num
  have hh : 0 < caliperCutoff*r := mul_pos (by norm_num [caliperCutoff]) hr'.1
  have hc : caliperCutoff*r < caliperCutoff := by
    nlinarith [show 0 < caliperCutoff by norm_num [caliperCutoff]]
  have H := linear_caliper_masses (caliperCutoff*r) hh hc
  refine ⟨hh, hc, H.2.2.2, H.1, H.2.1, ?_, linear_smooth _ hh hc⟩
  rw [H.2.2.1]
  norm_num [caliperCutoff]
  ring

lemma power_normalized (m : ℕ) :
    (∫ x in (0:ℝ)..4, ((m:ℝ)+1)*x^m/4^(m+1)) = 1 := by
  rw [polynomial_integral]
  simp

lemma power_nine : caliperProbability (powerCaliperDensity 9) (49/125) = 4609141/5401600 := by
  rw [power_formula 9 (49/125) (by norm_num) (by norm_num [caliperCutoff])]
  norm_num [caliperCutoff]

end caliper_counterexample


theorem caliper_counterexamples_proof :
    (∫ x in (0:ℝ)..4, x/8) = 1 ∧
    (∀ r ∈ ({(1/10:ℝ),3/20,1/5} : Finset ℝ),
      let h := caliperCutoff*r;
      0 < h ∧ h < caliperCutoff ∧
      (∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h), 0 < linearCaliperDensity x) ∧
      caliperAbove linearCaliperDensity h = (2*caliperCutoff*h+h^2)/16 ∧
      caliperBelow linearCaliperDensity h = (2*caliperCutoff*h-h^2)/16 ∧
      caliperProbability linearCaliperDensity h = 1/2+r/4 ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) linearCaliperDensity (Ioo (caliperCutoff-h) (caliperCutoff+h))) ∧
    caliperProbability linearCaliperDensity (caliperCutoff/10) = 21/40 ∧
    caliperProbability linearCaliperDensity (caliperCutoff*3/20) = 43/80 ∧
    caliperProbability linearCaliperDensity (caliperCutoff/5) = 11/20 ∧
    caliperAbove linearCaliperDensity (caliperCutoff/5) = 26411/250000 ∧
    caliperBelow linearCaliperDensity (caliperCutoff/5) = 21609/250000 ∧
    ((caliperCutoff-caliperCutoff/10 = 441/250 ∧ caliperCutoff+caliperCutoff/10 = 539/250) ∧
      (caliperCutoff-caliperCutoff*3/20 = 833/500 ∧ caliperCutoff+caliperCutoff*3/20 = 1127/500) ∧
      (caliperCutoff-caliperCutoff/5 = 196/125 ∧ caliperCutoff+caliperCutoff/5 = 294/125)) ∧
    (∀ k : ℕ, k ≤ 19 → (binomialTail 19 k (1/2) ≤ 1/20 ↔ 14 ≤ k)) ∧
    (∀ M : ℕ, 19 ≤ M →
      let μ := caliperDataLaw M linearCaliperDensity;
      μ.real {X | caliperCount (caliperCutoff/5) X = 19} > 0 →
      μ.real ({X | caliperCount (caliperCutoff/5) X = 19} ∩
        {X | binomialTail 19 (caliperSuccesses (caliperCutoff/5) X) (1/2) ≤ 1/20}) /
        μ.real {X | caliperCount (caliperCutoff/5) X = 19} = binomialTail 19 14 (11/20)) ∧
    (1/20:ℝ) < binomialTail 19 14 (11/20) ∧
    binomialTail 12 9 (1/2) = 299/4096 ∧
    binomialTail 12 9 (21/40) = 336637329302285487/3355443200000000000 ∧
    binomialTail 15 11 (1/2) = 1941/32768 ∧
    binomialTail 15 11 (43/80) = 3589476431322242287677900507/35184372088832000000000000000 ∧
    binomialTail 19 14 (1/2) = 2083/65536 ∧
    binomialTail 19 14 (11/20) = 50930691593528557166389/655360000000000000000000 ∧
    (∀ m : ℕ, 1 ≤ m →
      (∫ x in (0:ℝ)..4, ((m:ℝ)+1)*x^m/4^(m+1)) = 1 ∧
      (∀ h : ℝ, 0 < h → h < caliperCutoff →
        (∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h), 0 < powerCaliperDensity m x) ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (powerCaliperDensity m) (Ioo (caliperCutoff-h) (caliperCutoff+h)) ∧
        caliperProbability (powerCaliperDensity m) h =
          ((caliperCutoff+h)^(m+1)-caliperCutoff^(m+1))/
          ((caliperCutoff+h)^(m+1)-(caliperCutoff-h)^(m+1)))) ∧
    (∀ h : ℝ, 0 < h → h < caliperCutoff →
      Tendsto (fun m : ℕ => caliperProbability (powerCaliperDensity m) h) atTop (𝓝 1)) ∧
    caliperProbability (powerCaliperDensity 9) (49/125) = 4609141/5401600 ∧
    (∀ θ x : ℝ, 0 ≤ x → (gaussianReal θ 1).real {t | |t| ≤ x} = foldedNormalCDF θ x) ∧
    (∀ θ : ℝ, intervalCoverage (gaussianReal θ 1) id θ normalCritical = 19/20) ∧
    ((644747758104/10^12:ℝ) ≤ foldedCaliperProbability (7/2) (49/125) ∧
      foldedCaliperProbability (7/2) (49/125) ≤ 644747758105/10^12) ∧
    ((280413461677/10^12:ℝ) ≤ binomialTail 19 14 (foldedCaliperProbability (7/2) (49/125)) ∧
      binomialTail 19 14 (foldedCaliperProbability (7/2) (49/125)) ≤ 280413461678/10^12) ∧
    ((318944499071/10^12:ℝ) ≤ foldedCaliperProbability 0 (49/125) ∧
      foldedCaliperProbability 0 (49/125) ≤ 318944499072/10^12) := by
  rcases linear_caliper_witness with ⟨hnorm, p1, p2, p3, hA, hB, hgt⟩
  rcases caliper_exact_tails with ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩
  refine ⟨hnorm, caliper_counterexample.linear_windows, p1, p2, p3, hA, hB,
    ?_, ?_, ?_, t10, t1, t2, t3, t4, t5, t6, ?_, caliper_counterexample.power_limit,
    caliper_counterexample.power_nine,
    caliper_counterexample.folded_gaussian_formula_coverage.1,
    caliper_counterexample.folded_gaussian_formula_coverage.2,
    ?_, caliper_counterexample.folded_tail, ?_⟩
  · norm_num [caliperCutoff]
  · intro k hk
    exact caliper_counterexample.rejection_cutoff k
  · intro M hM
    dsimp only
    intro hn
    exact caliper_counterexample.linear_rejection M hn
  · intro m hm
    refine ⟨caliper_counterexample.power_normalized m, ?_⟩
    intro h hh hc
    exact ⟨(caliper_counterexample.power_positive_smooth m h hh hc).1,
      (caliper_counterexample.power_positive_smooth m h hh hc).2,
      caliper_counterexample.power_formula m h hh hc⟩
  · have hp := caliper_counterexample.folded_shift
    constructor <;> linarith [hp.1, hp.2]
  · have hp := caliper_counterexample.folded_zero
    constructor <;> linarith [hp.1, hp.2]


end
end AronowAudit.P033.Wave1
