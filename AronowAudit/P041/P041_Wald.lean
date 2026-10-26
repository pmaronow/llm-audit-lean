import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real

noncomputable section
namespace AronowAudit.P041

open scoped BigOperators

/-- "σ=s/h", P041-T2 and P041-T8: the delta-method log-hazard standard
error from a printed HR and standard error on the HR scale (S6/S9). -/
def logHazardSE (h s : ℝ) : ℝ := s/h

/-- "z(h,s)=h log(h)/s", P041-T2 / P041-T8, calculated
from the S6/S9 printed pairs. This is not a formula printed in the paper. -/
def hazardWald (h s : ℝ) : ℝ := h * Real.log h / s

/-- "p=2 Φ(-|z|)": Φ is the CDF of the
actual mean-zero variance-one Gaussian probability measure in Mathlib. -/
def normalTwoSided (z : ℝ) : ℝ :=
  2 * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-|z|)

/-- Closed three-decimal rounding interval, allowing either rounding endpoint. -/
def printedInterval (v x : ℝ) : Prop := v-0.0005 ≤ x ∧ x ≤ v+0.0005

/-- "exp(log h ± (49/25)σF)", P041-T2(b): a 95% Wald interval using
the target's stipulated multiplier 1.96, not the exact normal quantile. -/
def hazardWaldInterval (h s : ℝ) : Set ℝ :=
  Set.Icc (Real.exp (Real.log h - (49/25)*logHazardSE h s))
    (Real.exp (Real.log h + (49/25)*logHazardSE h s))

/-- "zd=(log hF-log hA)/sqrt(σF²+σA²)", P041-T2(c): the
independent-samples comparison specified by the target. -/
def betweenHazardWald (hF sF hA sA : ℝ) : ℝ :=
  (Real.log hF - Real.log hA) /
    Real.sqrt ((logHazardSE hF sF)^2 + (logHazardSE hA sA)^2)

/-- Rational partial series for half log((1+x)/(1-x)), as used in
Mathlib's sum_range_le_log_div. -/
def logSeries (x : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, x^(2*j+1)/(2*j+1)

/-- Finite certificate underlying P041-T2/T8: for 0<h<1 the atanh
series bounds -log h above and below. This uses Mathlib's proved remainder
bound; no external numerical certificate is assumed as an axiom. -/
theorem neg_log_certificate (h : ℝ) (h0 : 0 < h) (h1 : h < 1) (n : ℕ) :
    2*logSeries ((1-h)/(1+h)) n ≤ -Real.log h ∧
    -Real.log h ≤ 2*(logSeries ((1-h)/(1+h)) n +
      ((1-h)/(1+h))^(2*n+1)/(1-((1-h)/(1+h))^2)) := by
  have hd : 0 < 1+h := by linarith
  have hq0 : 0 ≤ (1-h)/(1+h) := by positivity
  have hq1 : (1-h)/(1+h) < 1 := by apply (div_lt_iff₀ hd).2; linarith
  have he : (1+(1-h)/(1+h))/(1-(1-h)/(1+h)) = h⁻¹ := by
    field_simp [ne_of_gt h0, ne_of_gt hd]
    <;> ring
  have hl := Real.sum_range_le_log_div hq0 hq1 n
  have hu := Real.log_div_le_sum_range_add hq0 hq1 n
  rw [he, Real.log_inv] at hl hu
  change logSeries ((1-h)/(1+h)) n ≤ 1/2 * (-Real.log h) at hl
  change 1/2 * (-Real.log h) ≤ logSeries ((1-h)/(1+h)) n +
    ((1-h)/(1+h))^(2*n+1)/(1-((1-h)/(1+h))^2) at hu
  constructor <;> linarith

/-- P041-T2/T8 finite analytic lemma: above exp(-1), -h log h is
antitone, so numerator bounds are attained at opposite endpoints. -/
theorem wald_numerator_above (l u h : ℝ) (hl : 0 < l)
    (hlh : l ≤ h) (hhu : h ≤ u) (hlog : -1 ≤ Real.log l) :
    u*(-Real.log u) ≤ h*(-Real.log h) ∧ h*(-Real.log h) ≤ l*(-Real.log l) := by
  have he : Real.exp (-1) ≤ l := (Real.le_log_iff_exp_le hl).1 hlog
  have hh : Real.exp (-1) ≤ h := le_trans he hlh
  have hu : Real.exp (-1) ≤ u := le_trans hh hhu
  have h₁ := Real.mul_log_strictMonoOn.monotoneOn hh hu hhu
  have h₂ := Real.mul_log_strictMonoOn.monotoneOn he hh hlh
  constructor <;> nlinarith

/-- P041-T8 finite analytic lemma: below exp(-1), -h log h is
monotone, so numerator bounds use the endpoints in the same order. -/
theorem wald_numerator_below (l u h : ℝ) (hl : 0 < l)
    (hlh : l ≤ h) (hhu : h ≤ u) (hlog : Real.log u ≤ -1) :
    l*(-Real.log l) ≤ h*(-Real.log h) ∧ h*(-Real.log h) ≤ u*(-Real.log u) := by
  have hu0 : 0 < u := lt_of_lt_of_le (lt_of_lt_of_le hl hlh) hhu
  have he : u ≤ Real.exp (-1) := (Real.log_le_iff_le_exp hu0).1 hlog
  have hh : h ≤ Real.exp (-1) := le_trans hhu he
  have hel : l ≤ Real.exp (-1) := le_trans hlh hh
  have h₁ := Real.mul_log_strictAntiOn.antitoneOn
    (show l ∈ Set.Icc 0 (Real.exp (-1)) from ⟨hl.le,hel⟩)
    (show h ∈ Set.Icc 0 (Real.exp (-1)) from ⟨(lt_of_lt_of_le hl hlh).le,hh⟩) hlh
  have h₂ := Real.mul_log_strictAntiOn.antitoneOn
    (show h ∈ Set.Icc 0 (Real.exp (-1)) from ⟨(lt_of_lt_of_le hl hlh).le,hh⟩)
    (show u ∈ Set.Icc 0 (Real.exp (-1)) from ⟨hu0.le,he⟩) hhu
  constructor <;> nlinarith

/-- Absolute Wald statistic for a ratio below one, P041-T2/T8. -/
theorem abs_hazard_wald (h s : ℝ) (h0 : 0 < h) (h1 : h < 1) (hs : 0 < s) :
    |hazardWald h s| = h*(-Real.log h)/s := by
  have hn := Real.log_neg h0 h1
  simp [hazardWald, abs_div, abs_mul, abs_of_pos h0, abs_of_neg hn, abs_of_pos hs]


/-- Rational endpoint logarithm enclosure for former, targets P041-T2/T8/T11. -/
theorem log_former_l :
    (0.37033:ℝ) < -Real.log (1381/2000:ℝ) ∧ -Real.log (1381/2000:ℝ) < 0.37034 := by
  have hc := neg_log_certificate (1381/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational endpoint logarithm enclosure for former, targets P041-T2/T8/T11. -/
theorem log_former_u :
    (0.36889:ℝ) < -Real.log (1383/2000:ℝ) ∧ -Real.log (1383/2000:ℝ) < 0.36890 := by
  have hc := neg_log_certificate (1383/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Wald bounds throughout the rounding rectangle of (0.691,0.318),
targets P041-T2/T8/T11; proved by numerator monotonicity and endpoint certificates. -/
theorem wald_former_rounding (h s : ℝ)
    (hh : printedInterval 0.691 h) (hs : printedInterval 0.318 s) :
    0.80 < |hazardWald h s| ∧ |hazardWald h s| < 0.81 := by
  rcases hh with ⟨hlo,hhi⟩
  rcases hs with ⟨slo,shi⟩
  have h0 : 0 < h := by linarith
  have h1 : h < 1 := by linarith
  have s0 : 0 < s := by linarith
  have hl := log_former_l
  have hu := log_former_u
  have hn := wald_numerator_above (1381/2000:ℝ) (1383/2000:ℝ) h (by norm_num)
    (by linarith) (by linarith) (by linarith [log_former_l])
  rw [abs_hazard_wald h s h0 h1 s0]
  constructor
  · apply (lt_div_iff₀ s0).2
    nlinarith [hn.1, hu.1]
  · apply (div_lt_iff₀ s0).2
    nlinarith [hn.2, hl.2]

/-- Rational endpoint logarithm enclosure for active, targets P041-T2/T8/T11. -/
theorem log_active_l :
    (0.46441:ℝ) < -Real.log (1257/2000:ℝ) ∧ -Real.log (1257/2000:ℝ) < 0.46442 := by
  have hc := neg_log_certificate (1257/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational endpoint logarithm enclosure for active, targets P041-T2/T8/T11. -/
theorem log_active_u :
    (0.46282:ℝ) < -Real.log (1259/2000:ℝ) ∧ -Real.log (1259/2000:ℝ) < 0.46283 := by
  have hc := neg_log_certificate (1259/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith


/-- Rational endpoint logarithm enclosure for pooled_adjusted, targets P041-T2/T8/T11. -/
theorem log_pooled_adjusted_l :
    (0.40122:ℝ) < -Real.log (1339/2000:ℝ) ∧ -Real.log (1339/2000:ℝ) < 0.40123 := by
  have hc := neg_log_certificate (1339/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational endpoint logarithm enclosure for pooled_adjusted, targets P041-T2/T8/T11. -/
theorem log_pooled_adjusted_u :
    (0.39973:ℝ) < -Real.log (1341/2000:ℝ) ∧ -Real.log (1341/2000:ℝ) < 0.39974 := by
  have hc := neg_log_certificate (1341/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Wald bounds throughout the rounding rectangle of (0.670,0.095),
targets P041-T2/T8/T11; proved by numerator monotonicity and endpoint certificates. -/
theorem wald_pooled_adjusted_rounding (h s : ℝ)
    (hh : printedInterval 0.670 h) (hs : printedInterval 0.095 s) :
    2.80 < |hazardWald h s| ∧ |hazardWald h s| < 2.85 := by
  rcases hh with ⟨hlo,hhi⟩
  rcases hs with ⟨slo,shi⟩
  have h0 : 0 < h := by linarith
  have h1 : h < 1 := by linarith
  have s0 : 0 < s := by linarith
  have hl := log_pooled_adjusted_l
  have hu := log_pooled_adjusted_u
  have hn := wald_numerator_above (1339/2000:ℝ) (1341/2000:ℝ) h (by norm_num)
    (by linarith) (by linarith) (by linarith [log_pooled_adjusted_l])
  rw [abs_hazard_wald h s h0 h1 s0]
  constructor
  · apply (lt_div_iff₀ s0).2
    nlinarith [hn.1, hu.1]
  · apply (div_lt_iff₀ s0).2
    nlinarith [hn.2, hl.2]

/-- Rational endpoint logarithm enclosure for cited_first_half, targets P041-T2/T8/T11. -/
theorem log_cited_first_half_l :
    (0.73501:ℝ) < -Real.log (959/2000:ℝ) ∧ -Real.log (959/2000:ℝ) < 0.73502 := by
  have hc := neg_log_certificate (959/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational endpoint logarithm enclosure for cited_first_half, targets P041-T2/T8/T11. -/
theorem log_cited_first_half_u :
    (0.73292:ℝ) < -Real.log (961/2000:ℝ) ∧ -Real.log (961/2000:ℝ) < 0.73293 := by
  have hc := neg_log_certificate (961/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Wald bounds throughout the rounding rectangle of (0.480,0.174),
targets P041-T2/T8/T11; proved by numerator monotonicity and endpoint certificates. -/
theorem wald_cited_first_half_rounding (h s : ℝ)
    (hh : printedInterval 0.480 h) (hs : printedInterval 0.174 s) :
    2.01 < |hazardWald h s| ∧ |hazardWald h s| < 2.04 := by
  rcases hh with ⟨hlo,hhi⟩
  rcases hs with ⟨slo,shi⟩
  have h0 : 0 < h := by linarith
  have h1 : h < 1 := by linarith
  have s0 : 0 < s := by linarith
  have hl := log_cited_first_half_l
  have hu := log_cited_first_half_u
  have hn := wald_numerator_above (959/2000:ℝ) (961/2000:ℝ) h (by norm_num)
    (by linarith) (by linarith) (by linarith [log_cited_first_half_l])
  rw [abs_hazard_wald h s h0 h1 s0]
  constructor
  · apply (lt_div_iff₀ s0).2
    nlinarith [hn.1, hu.1]
  · apply (div_lt_iff₀ s0).2
    nlinarith [hn.2, hl.2]

/-- Rational endpoint logarithm enclosure for positive_second_half, targets P041-T2/T8/T11. -/
theorem log_positive_second_half_l :
    (1.29645:ℝ) < -Real.log (547/2000:ℝ) ∧ -Real.log (547/2000:ℝ) < 1.29648 := by
  have hc := neg_log_certificate (547/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational endpoint logarithm enclosure for positive_second_half, targets P041-T2/T8/T11. -/
theorem log_positive_second_half_u :
    (1.29280:ℝ) < -Real.log (549/2000:ℝ) ∧ -Real.log (549/2000:ℝ) < 1.29283 := by
  have hc := neg_log_certificate (549/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Wald bounds throughout the rounding rectangle of (0.274,0.162),
targets P041-T2/T8/T11; proved by numerator monotonicity and endpoint certificates. -/
theorem wald_positive_second_half_rounding (h s : ℝ)
    (hh : printedInterval 0.274 h) (hs : printedInterval 0.162 s) :
    2.18 < |hazardWald h s| ∧ |hazardWald h s| < 2.20 := by
  rcases hh with ⟨hlo,hhi⟩
  rcases hs with ⟨slo,shi⟩
  have h0 : 0 < h := by linarith
  have h1 : h < 1 := by linarith
  have s0 : 0 < s := by linarith
  have hl := log_positive_second_half_l
  have hu := log_positive_second_half_u
  have hn := wald_numerator_below (547/2000:ℝ) (549/2000:ℝ) h (by norm_num)
    (by linarith) (by linarith) (by linarith [log_positive_second_half_u])
  rw [abs_hazard_wald h s h0 h1 s0]
  constructor
  · apply (lt_div_iff₀ s0).2
    nlinarith [hn.1, hl.1]
  · apply (div_lt_iff₀ s0).2
    nlinarith [hn.2, hu.2]

/-- Rational endpoint logarithm enclosure for northeast, targets P041-T2/T8/T11. -/
theorem log_northeast_l :
    (1.15359:ℝ) < -Real.log (631/2000:ℝ) ∧ -Real.log (631/2000:ℝ) < 1.15360 := by
  have hc := neg_log_certificate (631/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational endpoint logarithm enclosure for northeast, targets P041-T2/T8/T11. -/
theorem log_northeast_u :
    (1.15043:ℝ) < -Real.log (633/2000:ℝ) ∧ -Real.log (633/2000:ℝ) < 1.15044 := by
  have hc := neg_log_certificate (633/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Wald bounds throughout the rounding rectangle of (0.316,0.149),
targets P041-T2/T8/T11; proved by numerator monotonicity and endpoint certificates. -/
theorem wald_northeast_rounding (h s : ℝ)
    (hh : printedInterval 0.316 h) (hs : printedInterval 0.149 s) :
    2.43 < |hazardWald h s| ∧ |hazardWald h s| < 2.46 := by
  rcases hh with ⟨hlo,hhi⟩
  rcases hs with ⟨slo,shi⟩
  have h0 : 0 < h := by linarith
  have h1 : h < 1 := by linarith
  have s0 : 0 < s := by linarith
  have hl := log_northeast_l
  have hu := log_northeast_u
  have hn := wald_numerator_below (631/2000:ℝ) (633/2000:ℝ) h (by norm_num)
    (by linarith) (by linarith) (by linarith [log_northeast_u])
  rw [abs_hazard_wald h s h0 h1 s0]
  constructor
  · apply (lt_div_iff₀ s0).2
    nlinarith [hn.1, hl.1]
  · apply (div_lt_iff₀ s0).2
    nlinarith [hn.2, hu.2]

/-- Rational endpoint logarithm enclosure for living, targets P041-T2/T8/T11. -/
theorem log_living_l :
    (0.25553:ℝ) < -Real.log (1549/2000:ℝ) ∧ -Real.log (1549/2000:ℝ) < 0.25554 := by
  have hc := neg_log_certificate (1549/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational endpoint logarithm enclosure for living, targets P041-T2/T8/T11. -/
theorem log_living_u :
    (0.25424:ℝ) < -Real.log (1551/2000:ℝ) ∧ -Real.log (1551/2000:ℝ) < 0.25425 := by
  have hc := neg_log_certificate (1551/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Wald bounds throughout the rounding rectangle of (0.775,0.503),
targets P041-T2/T8/T11; proved by numerator monotonicity and endpoint certificates. -/
theorem wald_living_rounding (h s : ℝ)
    (hh : printedInterval 0.775 h) (hs : printedInterval 0.503 s) :
    0.39 < |hazardWald h s| ∧ |hazardWald h s| < 0.40 := by
  rcases hh with ⟨hlo,hhi⟩
  rcases hs with ⟨slo,shi⟩
  have h0 : 0 < h := by linarith
  have h1 : h < 1 := by linarith
  have s0 : 0 < s := by linarith
  have hl := log_living_l
  have hu := log_living_u
  have hn := wald_numerator_above (1549/2000:ℝ) (1551/2000:ℝ) h (by norm_num)
    (by linarith) (by linarith) (by linarith [log_living_l])
  rw [abs_hazard_wald h s h0 h1 s0]
  constructor
  · apply (lt_div_iff₀ s0).2
    nlinarith [hn.1, hu.1]
  · apply (div_lt_iff₀ s0).2
    nlinarith [hn.2, hl.2]

/-- Rational endpoint logarithm enclosure for deceased, targets P041-T2/T8/T11. -/
theorem log_deceased_l :
    (0.46760:ℝ) < -Real.log (1253/2000:ℝ) ∧ -Real.log (1253/2000:ℝ) < 0.46761 := by
  have hc := neg_log_certificate (1253/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational endpoint logarithm enclosure for deceased, targets P041-T2/T8/T11. -/
theorem log_deceased_u :
    (0.46601:ℝ) < -Real.log (251/400:ℝ) ∧ -Real.log (251/400:ℝ) < 0.46602 := by
  have hc := neg_log_certificate (251/400:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Wald bounds throughout the rounding rectangle of (0.627,0.406),
targets P041-T2/T8/T11; proved by numerator monotonicity and endpoint certificates. -/
theorem wald_deceased_rounding (h s : ℝ)
    (hh : printedInterval 0.627 h) (hs : printedInterval 0.406 s) :
    0.71 < |hazardWald h s| ∧ |hazardWald h s| < 0.73 := by
  rcases hh with ⟨hlo,hhi⟩
  rcases hs with ⟨slo,shi⟩
  have h0 : 0 < h := by linarith
  have h1 : h < 1 := by linarith
  have s0 : 0 < s := by linarith
  have hl := log_deceased_l
  have hu := log_deceased_u
  have hn := wald_numerator_above (1253/2000:ℝ) (251/400:ℝ) h (by norm_num)
    (by linarith) (by linarith) (by linarith [log_deceased_l])
  rw [abs_hazard_wald h s h0 h1 s0]
  constructor
  · apply (lt_div_iff₀ s0).2
    nlinarith [hn.1, hu.1]
  · apply (div_lt_iff₀ s0).2
    nlinarith [hn.2, hl.2]

/-- Endpoint monotonicity extends rational log certificates to an entire
rounding interval, used in P041-T2(b)-(c). -/
theorem neg_log_rectangle (l u h L U : ℝ) (hl : 0 < l) (hh : l ≤ h)
    (hu : h ≤ u) (hL : L < -Real.log u) (hU : -Real.log l < U) :
    L < -Real.log h ∧ -Real.log h < U := by
  have hp : 0 < h := lt_of_lt_of_le hl hh
  have h₁ := Real.log_le_log hl hh
  have h₂ := Real.log_le_log hp hu
  constructor <;> linarith

/-- P041-T2(a), corrected nondetection: throughout the former-senator
printed rounding rectangle 0.80<|z|<0.81<1. -/
theorem corrected_former_nondetection (h s : ℝ)
    (hh : printedInterval 0.691 h) (hs : printedInterval 0.318 s) :
    0.80 < |hazardWald h s| ∧ |hazardWald h s| < 0.81 ∧ |hazardWald h s| < 1 := by
  obtain ⟨hl,hu⟩ := wald_former_rounding h s hh hs
  exact ⟨hl,hu,lt_trans hu (by norm_num)⟩

/-- P041-T2(b)-(c), reusable finite enclosures of log estimates and
delta-method log standard errors over all four rounding intervals. -/
theorem former_active_log_se_enclosures (hF sF hA sA : ℝ)
    (hf : printedInterval 0.691 hF) (sf : printedInterval 0.318 sF)
    (ha : printedInterval 0.629 hA) (sa : printedInterval 0.091 sA) :
    (0.36889 < -Real.log hF ∧ -Real.log hF < 0.37034) ∧
    (0.46282 < -Real.log hA ∧ -Real.log hA < 0.46442) ∧
    (0.459 < logHazardSE hF sF ∧ logHazardSE hF sF < 0.462) ∧
    (0.143 < logHazardSE hA sA ∧ logHazardSE hA sA < 0.146) := by
  rcases hf with ⟨hfl,hfu⟩; rcases sf with ⟨sfl,sfu⟩
  rcases ha with ⟨hal,hau⟩; rcases sa with ⟨sal,sau⟩
  refine ⟨neg_log_rectangle (1381/2000) (1383/2000) hF 0.36889 0.37034
    (by norm_num) (by linarith) (by linarith) log_former_u.1 log_former_l.2,
    neg_log_rectangle (1257/2000) (1259/2000) hA 0.46282 0.46442
    (by norm_num) (by linarith) (by linarith) log_active_u.1 log_active_l.2, ?_, ?_⟩
  · have hp : 0 < hF := by linarith
    unfold logHazardSE
    constructor
    · apply (lt_div_iff₀ hp).2; nlinarith
    · apply (div_lt_iff₀ hp).2; nlinarith
  · have hp : 0 < hA := by linarith
    unfold logHazardSE
    constructor
    · apply (lt_div_iff₀ hp).2; nlinarith
    · apply (div_lt_iff₀ hp).2; nlinarith

/-- P041-T2(b), corrected imprecision: the former-senator 95% Wald interval
contains both 1 and every possible active-senator estimate. The inequalities
hold for every choice in all four rounding intervals. -/
theorem corrected_former_imprecision (hF sF hA sA : ℝ)
    (hf : printedInterval 0.691 hF) (sf : printedInterval 0.318 sF)
    (ha : printedInterval 0.629 hA) (sa : printedInterval 0.091 sA) :
    |Real.log hF - Real.log hA| < 0.21 * logHazardSE hF sF ∧
    0.21 * logHazardSE hF sF < (49/25) * logHazardSE hF sF ∧
    |Real.log hF| < (49/25) * logHazardSE hF sF ∧
    1 ∈ hazardWaldInterval hF sF ∧ hA ∈ hazardWaldInterval hF sF := by
  obtain ⟨⟨f₁,f₂⟩,⟨a₁,a₂⟩,⟨σ₁,σ₂⟩,_⟩ :=
    former_active_log_se_enclosures hF sF hA sA hf sf ha sa
  have hd : 0 < Real.log hF - Real.log hA := by linarith
  have hneg : Real.log hF < 0 := by linarith
  have hb : |Real.log hF - Real.log hA| < 0.21 * logHazardSE hF sF := by
    rw [abs_of_pos hd]; linarith
  have hm : 0.21 * logHazardSE hF sF < (49/25) * logHazardSE hF sF := by linarith
  have hz : |Real.log hF| < (49/25) * logHazardSE hF sF := by
    rw [abs_of_neg hneg]; linarith
  refine ⟨hb,hm,hz,?_,?_⟩
  · change Real.exp (Real.log hF-(49/25)*logHazardSE hF sF) ≤ 1 ∧
      1 ≤ Real.exp (Real.log hF+(49/25)*logHazardSE hF sF)
    constructor
    · simpa only [Real.exp_zero] using
        Real.exp_le_exp.mpr (show Real.log hF-(49/25)*logHazardSE hF sF ≤ 0 by linarith)
    · simpa only [Real.exp_zero] using
        Real.exp_le_exp.mpr (show 0 ≤ Real.log hF+(49/25)*logHazardSE hF sF by linarith)
  · have hA0 : 0 < hA := by rcases ha with ⟨hl,hu⟩; linarith
    change Real.exp (Real.log hF-(49/25)*logHazardSE hF sF) ≤ hA ∧
      hA ≤ Real.exp (Real.log hF+(49/25)*logHazardSE hF sF)
    constructor
    · calc
        _ ≤ Real.exp (Real.log hA) := Real.exp_le_exp.mpr (by rw [abs_of_pos hd] at hb; linarith)
        _ = hA := Real.exp_log hA0
    · calc
        hA = Real.exp (Real.log hA) := (Real.exp_log hA0).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- P041-T2(c): treating the samples as independent, throughout the
four rounding intervals 0.18<zd<0.21, so the estimates do not distinguish
the two relative effects. This finite bound does not assert population equality. -/
theorem corrected_between_relative_effects (hF sF hA sA : ℝ)
    (hf : printedInterval 0.691 hF) (sf : printedInterval 0.318 sF)
    (ha : printedInterval 0.629 hA) (sa : printedInterval 0.091 sA) :
    0.18 < betweenHazardWald hF sF hA sA ∧ betweenHazardWald hF sF hA sA < 0.21 := by
  obtain ⟨⟨f₁,f₂⟩,⟨a₁,a₂⟩,⟨σ₁,σ₂⟩,⟨τ₁,τ₂⟩⟩ :=
    former_active_log_se_enclosures hF sF hA sA hf sf ha sa
  have hn := Real.sqrt_nonneg ((logHazardSE hF sF)^2+(logHazardSE hA sA)^2)
  have he := Real.sq_sqrt (by positivity :
    0 ≤ (logHazardSE hF sF)^2+(logHazardSE hA sA)^2)
  have hdl : 0.48 < Real.sqrt ((logHazardSE hF sF)^2+(logHazardSE hA sA)^2) := by nlinarith
  have hdu : Real.sqrt ((logHazardSE hF sF)^2+(logHazardSE hA sA)^2) < 0.485 := by nlinarith
  have hp : 0 < Real.sqrt ((logHazardSE hF sF)^2+(logHazardSE hA sA)^2) := by linarith
  unfold betweenHazardWald
  constructor
  · apply (lt_div_iff₀ hp).2; nlinarith
  · apply (div_lt_iff₀ hp).2; nlinarith

/-- P041-T2(b) finite lemma: a small h interval gives rigorous enclosures
for both Wald interval exponents; s still ranges over its full printed interval. -/
theorem wald_exponents_cell (h s l u L U : ℝ) (hl : 0 < l) (hlh : l ≤ h)
    (hhu : h ≤ u) (sf : printedInterval 0.318 s)
    (hlg : L < -Real.log u) (hug : -Real.log l < U) :
    (-U-(49/25)*(0.3185/l) < Real.log h-(49/25)*logHazardSE h s) ∧
    (Real.log h-(49/25)*logHazardSE h s < -L-(49/25)*(0.3175/u)) ∧
    (-U+(49/25)*(0.3175/u) < Real.log h+(49/25)*logHazardSE h s) ∧
    (Real.log h+(49/25)*logHazardSE h s < -L+(49/25)*(0.3185/l)) := by
  have hh0 : 0 < h := lt_of_lt_of_le hl hlh
  rcases sf with ⟨sfl,sfu⟩
  have hs0 : 0 ≤ s := by linarith
  obtain ⟨hlg',hug'⟩ := neg_log_rectangle l u h L U hl hlh hhu hlg hug
  have hσl : 0.3175/u ≤ logHazardSE h s :=
    div_le_div₀ hs0 (by linarith) hh0 hhu
  have hσu : logHazardSE h s ≤ 0.3185/l :=
    div_le_div₀ (by norm_num) (by linarith) hl hlh
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

/-- Rational log endpoint certificate for P041-T2(b)'s Wald interval. -/
theorem wald_log279 : (1.27654:ℝ) < -Real.log (279/1000:ℝ) ∧ -Real.log (279/1000:ℝ) < 1.27657 := by
  have hc := neg_log_certificate (279/1000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational log endpoint certificate for P041-T2(b)'s Wald interval. -/
theorem wald_log282 : (1.26584:ℝ) < -Real.log (141/500:ℝ) ∧ -Real.log (141/500:ℝ) < 1.26587 := by
  have hc := neg_log_certificate (141/500:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational log endpoint certificate for P041-T2(b)'s Wald interval. -/
theorem wald_log_inv1700 : (0.53062:ℝ) < -Real.log (10/17:ℝ) ∧ -Real.log (10/17:ℝ) < 0.53063 := by
  have hc := neg_log_certificate (10/17:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational log endpoint certificate for P041-T2(b)'s Wald interval. -/
theorem wald_log_inv1706 : (0.53415:ℝ) < -Real.log (500/853:ℝ) ∧ -Real.log (500/853:ℝ) < 0.53416 := by
  have hc := neg_log_certificate (500/853:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational log endpoint certificate for P041-T2(b)'s Wald interval. -/
theorem wald_cell_log_0 : (0.37033:ℝ) < -Real.log (1381/2000:ℝ) ∧ -Real.log (1381/2000:ℝ) < 0.37034 := by
  have hc := neg_log_certificate (1381/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational log endpoint certificate for P041-T2(b)'s Wald interval. -/
theorem wald_cell_log_1 : (0.37015:ℝ) < -Real.log (221/320:ℝ) ∧ -Real.log (221/320:ℝ) < 0.37016 := by
  have hc := neg_log_certificate (221/320:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational log endpoint certificate for P041-T2(b)'s Wald interval. -/
theorem wald_cell_log_2 : (0.36997:ℝ) < -Real.log (2763/4000:ℝ) ∧ -Real.log (2763/4000:ℝ) < 0.36998 := by
  have hc := neg_log_certificate (2763/4000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational log endpoint certificate for P041-T2(b)'s Wald interval. -/
theorem wald_cell_log_3 : (0.36979:ℝ) < -Real.log (5527/8000:ℝ) ∧ -Real.log (5527/8000:ℝ) < 0.36980 := by
  have hc := neg_log_certificate (5527/8000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational log endpoint certificate for P041-T2(b)'s Wald interval. -/
theorem wald_cell_log_4 : (0.36961:ℝ) < -Real.log (691/1000:ℝ) ∧ -Real.log (691/1000:ℝ) < 0.36962 := by
  have hc := neg_log_certificate (691/1000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational log endpoint certificate for P041-T2(b)'s Wald interval. -/
theorem wald_cell_log_5 : (0.36943:ℝ) < -Real.log (5529/8000:ℝ) ∧ -Real.log (5529/8000:ℝ) < 0.36944 := by
  have hc := neg_log_certificate (5529/8000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational log endpoint certificate for P041-T2(b)'s Wald interval. -/
theorem wald_cell_log_6 : (0.36925:ℝ) < -Real.log (553/800:ℝ) ∧ -Real.log (553/800:ℝ) < 0.36926 := by
  have hc := neg_log_certificate (553/800:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational log endpoint certificate for P041-T2(b)'s Wald interval. -/
theorem wald_cell_log_7 : (0.36907:ℝ) < -Real.log (5531/8000:ℝ) ∧ -Real.log (5531/8000:ℝ) < 0.36908 := by
  have hc := neg_log_certificate (5531/8000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Rational log endpoint certificate for P041-T2(b)'s Wald interval. -/
theorem wald_cell_log_8 : (0.36889:ℝ) < -Real.log (1383/2000:ℝ) ∧ -Real.log (1383/2000:ℝ) < 0.36890 := by
  have hc := neg_log_certificate (1383/2000:ℝ) (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Cell 1/8 of the former-senator rounding interval, P041-T2(b). -/
theorem former_interval_cell_0 (h s : ℝ) (hl : (1381/2000:ℝ) ≤ h) (hu : h ≤ (221/320:ℝ))
    (sf : printedInterval 0.318 s) :
    0.279 < Real.exp (Real.log h-(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h-(49/25)*logHazardSE h s) < 0.282 ∧
    1.700 < Real.exp (Real.log h+(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h+(49/25)*logHazardSE h s) < 1.706 := by
  obtain ⟨x₁,x₂,x₃,x₄⟩ := wald_exponents_cell h s (1381/2000:ℝ) (221/320:ℝ) 0.37015 0.37034
    (by norm_num) hl hu sf wald_cell_log_1.1 wald_cell_log_0.2
  have log279 := wald_log279
  have log282 := wald_log282
  have log1700 := wald_log_inv1700
  have log1706 := wald_log_inv1706
  have e₁ : (10/17:ℝ) = (1.700:ℝ)⁻¹ := by norm_num
  have e₂ : (500/853:ℝ) = (1.706:ℝ)⁻¹ := by norm_num
  rw [e₁,Real.log_inv,neg_neg] at log1700
  rw [e₂,Real.log_inv,neg_neg] at log1706
  norm_num at x₁ x₂ x₃ x₄
  refine ⟨?_,?_,?_,?_⟩
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log279.1]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log282.2]
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log1700.2]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log1706.1]

/-- Cell 2/8 of the former-senator rounding interval, P041-T2(b). -/
theorem former_interval_cell_1 (h s : ℝ) (hl : (221/320:ℝ) ≤ h) (hu : h ≤ (2763/4000:ℝ))
    (sf : printedInterval 0.318 s) :
    0.279 < Real.exp (Real.log h-(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h-(49/25)*logHazardSE h s) < 0.282 ∧
    1.700 < Real.exp (Real.log h+(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h+(49/25)*logHazardSE h s) < 1.706 := by
  obtain ⟨x₁,x₂,x₃,x₄⟩ := wald_exponents_cell h s (221/320:ℝ) (2763/4000:ℝ) 0.36997 0.37016
    (by norm_num) hl hu sf wald_cell_log_2.1 wald_cell_log_1.2
  have log279 := wald_log279
  have log282 := wald_log282
  have log1700 := wald_log_inv1700
  have log1706 := wald_log_inv1706
  have e₁ : (10/17:ℝ) = (1.700:ℝ)⁻¹ := by norm_num
  have e₂ : (500/853:ℝ) = (1.706:ℝ)⁻¹ := by norm_num
  rw [e₁,Real.log_inv,neg_neg] at log1700
  rw [e₂,Real.log_inv,neg_neg] at log1706
  norm_num at x₁ x₂ x₃ x₄
  refine ⟨?_,?_,?_,?_⟩
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log279.1]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log282.2]
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log1700.2]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log1706.1]

/-- Cell 3/8 of the former-senator rounding interval, P041-T2(b). -/
theorem former_interval_cell_2 (h s : ℝ) (hl : (2763/4000:ℝ) ≤ h) (hu : h ≤ (5527/8000:ℝ))
    (sf : printedInterval 0.318 s) :
    0.279 < Real.exp (Real.log h-(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h-(49/25)*logHazardSE h s) < 0.282 ∧
    1.700 < Real.exp (Real.log h+(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h+(49/25)*logHazardSE h s) < 1.706 := by
  obtain ⟨x₁,x₂,x₃,x₄⟩ := wald_exponents_cell h s (2763/4000:ℝ) (5527/8000:ℝ) 0.36979 0.36998
    (by norm_num) hl hu sf wald_cell_log_3.1 wald_cell_log_2.2
  have log279 := wald_log279
  have log282 := wald_log282
  have log1700 := wald_log_inv1700
  have log1706 := wald_log_inv1706
  have e₁ : (10/17:ℝ) = (1.700:ℝ)⁻¹ := by norm_num
  have e₂ : (500/853:ℝ) = (1.706:ℝ)⁻¹ := by norm_num
  rw [e₁,Real.log_inv,neg_neg] at log1700
  rw [e₂,Real.log_inv,neg_neg] at log1706
  norm_num at x₁ x₂ x₃ x₄
  refine ⟨?_,?_,?_,?_⟩
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log279.1]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log282.2]
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log1700.2]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log1706.1]

/-- Cell 4/8 of the former-senator rounding interval, P041-T2(b). -/
theorem former_interval_cell_3 (h s : ℝ) (hl : (5527/8000:ℝ) ≤ h) (hu : h ≤ (691/1000:ℝ))
    (sf : printedInterval 0.318 s) :
    0.279 < Real.exp (Real.log h-(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h-(49/25)*logHazardSE h s) < 0.282 ∧
    1.700 < Real.exp (Real.log h+(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h+(49/25)*logHazardSE h s) < 1.706 := by
  obtain ⟨x₁,x₂,x₃,x₄⟩ := wald_exponents_cell h s (5527/8000:ℝ) (691/1000:ℝ) 0.36961 0.36980
    (by norm_num) hl hu sf wald_cell_log_4.1 wald_cell_log_3.2
  have log279 := wald_log279
  have log282 := wald_log282
  have log1700 := wald_log_inv1700
  have log1706 := wald_log_inv1706
  have e₁ : (10/17:ℝ) = (1.700:ℝ)⁻¹ := by norm_num
  have e₂ : (500/853:ℝ) = (1.706:ℝ)⁻¹ := by norm_num
  rw [e₁,Real.log_inv,neg_neg] at log1700
  rw [e₂,Real.log_inv,neg_neg] at log1706
  norm_num at x₁ x₂ x₃ x₄
  refine ⟨?_,?_,?_,?_⟩
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log279.1]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log282.2]
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log1700.2]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log1706.1]

/-- Cell 5/8 of the former-senator rounding interval, P041-T2(b). -/
theorem former_interval_cell_4 (h s : ℝ) (hl : (691/1000:ℝ) ≤ h) (hu : h ≤ (5529/8000:ℝ))
    (sf : printedInterval 0.318 s) :
    0.279 < Real.exp (Real.log h-(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h-(49/25)*logHazardSE h s) < 0.282 ∧
    1.700 < Real.exp (Real.log h+(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h+(49/25)*logHazardSE h s) < 1.706 := by
  obtain ⟨x₁,x₂,x₃,x₄⟩ := wald_exponents_cell h s (691/1000:ℝ) (5529/8000:ℝ) 0.36943 0.36962
    (by norm_num) hl hu sf wald_cell_log_5.1 wald_cell_log_4.2
  have log279 := wald_log279
  have log282 := wald_log282
  have log1700 := wald_log_inv1700
  have log1706 := wald_log_inv1706
  have e₁ : (10/17:ℝ) = (1.700:ℝ)⁻¹ := by norm_num
  have e₂ : (500/853:ℝ) = (1.706:ℝ)⁻¹ := by norm_num
  rw [e₁,Real.log_inv,neg_neg] at log1700
  rw [e₂,Real.log_inv,neg_neg] at log1706
  norm_num at x₁ x₂ x₃ x₄
  refine ⟨?_,?_,?_,?_⟩
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log279.1]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log282.2]
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log1700.2]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log1706.1]

/-- Cell 6/8 of the former-senator rounding interval, P041-T2(b). -/
theorem former_interval_cell_5 (h s : ℝ) (hl : (5529/8000:ℝ) ≤ h) (hu : h ≤ (553/800:ℝ))
    (sf : printedInterval 0.318 s) :
    0.279 < Real.exp (Real.log h-(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h-(49/25)*logHazardSE h s) < 0.282 ∧
    1.700 < Real.exp (Real.log h+(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h+(49/25)*logHazardSE h s) < 1.706 := by
  obtain ⟨x₁,x₂,x₃,x₄⟩ := wald_exponents_cell h s (5529/8000:ℝ) (553/800:ℝ) 0.36925 0.36944
    (by norm_num) hl hu sf wald_cell_log_6.1 wald_cell_log_5.2
  have log279 := wald_log279
  have log282 := wald_log282
  have log1700 := wald_log_inv1700
  have log1706 := wald_log_inv1706
  have e₁ : (10/17:ℝ) = (1.700:ℝ)⁻¹ := by norm_num
  have e₂ : (500/853:ℝ) = (1.706:ℝ)⁻¹ := by norm_num
  rw [e₁,Real.log_inv,neg_neg] at log1700
  rw [e₂,Real.log_inv,neg_neg] at log1706
  norm_num at x₁ x₂ x₃ x₄
  refine ⟨?_,?_,?_,?_⟩
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log279.1]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log282.2]
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log1700.2]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log1706.1]

/-- Cell 7/8 of the former-senator rounding interval, P041-T2(b). -/
theorem former_interval_cell_6 (h s : ℝ) (hl : (553/800:ℝ) ≤ h) (hu : h ≤ (5531/8000:ℝ))
    (sf : printedInterval 0.318 s) :
    0.279 < Real.exp (Real.log h-(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h-(49/25)*logHazardSE h s) < 0.282 ∧
    1.700 < Real.exp (Real.log h+(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h+(49/25)*logHazardSE h s) < 1.706 := by
  obtain ⟨x₁,x₂,x₃,x₄⟩ := wald_exponents_cell h s (553/800:ℝ) (5531/8000:ℝ) 0.36907 0.36926
    (by norm_num) hl hu sf wald_cell_log_7.1 wald_cell_log_6.2
  have log279 := wald_log279
  have log282 := wald_log282
  have log1700 := wald_log_inv1700
  have log1706 := wald_log_inv1706
  have e₁ : (10/17:ℝ) = (1.700:ℝ)⁻¹ := by norm_num
  have e₂ : (500/853:ℝ) = (1.706:ℝ)⁻¹ := by norm_num
  rw [e₁,Real.log_inv,neg_neg] at log1700
  rw [e₂,Real.log_inv,neg_neg] at log1706
  norm_num at x₁ x₂ x₃ x₄
  refine ⟨?_,?_,?_,?_⟩
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log279.1]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log282.2]
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log1700.2]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log1706.1]

/-- Cell 8/8 of the former-senator rounding interval, P041-T2(b). -/
theorem former_interval_cell_7 (h s : ℝ) (hl : (5531/8000:ℝ) ≤ h) (hu : h ≤ (1383/2000:ℝ))
    (sf : printedInterval 0.318 s) :
    0.279 < Real.exp (Real.log h-(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h-(49/25)*logHazardSE h s) < 0.282 ∧
    1.700 < Real.exp (Real.log h+(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h+(49/25)*logHazardSE h s) < 1.706 := by
  obtain ⟨x₁,x₂,x₃,x₄⟩ := wald_exponents_cell h s (5531/8000:ℝ) (1383/2000:ℝ) 0.36889 0.36908
    (by norm_num) hl hu sf wald_cell_log_8.1 wald_cell_log_7.2
  have log279 := wald_log279
  have log282 := wald_log282
  have log1700 := wald_log_inv1700
  have log1706 := wald_log_inv1706
  have e₁ : (10/17:ℝ) = (1.700:ℝ)⁻¹ := by norm_num
  have e₂ : (500/853:ℝ) = (1.706:ℝ)⁻¹ := by norm_num
  rw [e₁,Real.log_inv,neg_neg] at log1700
  rw [e₂,Real.log_inv,neg_neg] at log1706
  norm_num at x₁ x₂ x₃ x₄
  refine ⟨?_,?_,?_,?_⟩
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log279.1]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log282.2]
  · apply (Real.log_lt_iff_lt_exp (by norm_num)).1; linarith [log1700.2]
  · apply (Real.lt_log_iff_exp_lt (by norm_num)).1; linarith [log1706.1]

/-- P041-T2(b), additional quantitative Wald interval endpoint enclosures
throughout the printed former-senator rectangle. Proved by eight rational cells; the
interval-inclusion claims are also proved above. -/
theorem former_wald_endpoint_enclosures (h s : ℝ)
    (hh : printedInterval 0.691 h) (hs : printedInterval 0.318 s) :
    0.279 < Real.exp (Real.log h-(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h-(49/25)*logHazardSE h s) < 0.282 ∧
    1.700 < Real.exp (Real.log h+(49/25)*logHazardSE h s) ∧
    Real.exp (Real.log h+(49/25)*logHazardSE h s) < 1.706 := by
  rcases hh with ⟨hl,hu⟩
  by_cases h0 : h ≤ (221/320:ℝ)
  · exact former_interval_cell_0 h s (by linarith) h0 hs
  by_cases h1 : h ≤ (2763/4000:ℝ)
  · exact former_interval_cell_1 h s (by linarith) h1 hs
  by_cases h2 : h ≤ (5527/8000:ℝ)
  · exact former_interval_cell_2 h s (by linarith) h2 hs
  by_cases h3 : h ≤ (691/1000:ℝ)
  · exact former_interval_cell_3 h s (by linarith) h3 hs
  by_cases h4 : h ≤ (5529/8000:ℝ)
  · exact former_interval_cell_4 h s (by linarith) h4 hs
  by_cases h5 : h ≤ (553/800:ℝ)
  · exact former_interval_cell_5 h s (by linarith) h5 hs
  by_cases h6 : h ≤ (5531/8000:ℝ)
  · exact former_interval_cell_6 h s (by linarith) h6 hs
  exact former_interval_cell_7 h s (by linarith) (by linarith) hs

/-- Conventional strongest-tier star rule for S6/S9, P041-T8:
"*** when p<0.01, ** when 0.01≤p<0.05, * when 0.05≤p<0.10".
The paper's legend alone permits a weaker nested-cutoff reading. -/
def significanceTier (z : ℝ) : ℕ :=
  if normalTwoSided z < 0.01 then 3 else if normalTwoSided z < 0.05 then 2
  else if normalTwoSided z < 0.10 then 1 else 0

/-- P041-T8(i)-(iv), all four corrected Wald-statistic inequalities,
uniform in the printed rounding rectangles. These finite bounds use the
actual logarithm and are fully proved; they do not assume normal tail values. -/
theorem corrected_star_wald_bounds :
    (∀ h s : ℝ, printedInterval 0.670 h → printedInterval 0.095 s →
      2.80 < |hazardWald h s|) ∧
    (∀ h s : ℝ, printedInterval 0.480 h → printedInterval 0.174 s →
      2.01 < |hazardWald h s| ∧ |hazardWald h s| < 2.04) ∧
    (∀ h s : ℝ, printedInterval 0.274 h → printedInterval 0.162 s →
      2.18 < |hazardWald h s| ∧ |hazardWald h s| < 2.20) ∧
    (∀ h s : ℝ, printedInterval 0.316 h → printedInterval 0.149 s →
      2.43 < |hazardWald h s| ∧ |hazardWald h s| < 2.46) := by
  exact ⟨fun h s hh hs => (wald_pooled_adjusted_rounding h s hh hs).1,
    wald_cited_first_half_rounding, wald_positive_second_half_rounding,
    wald_northeast_rounding⟩


/-- P041-T8(v), literal nested significance versus strongest-tier reading:
the first three printed tiers assert weaker true cutoffs, whereas the Northeast
three-star assertion is false even as a nested 1% cutoff. This elementary
logical lemma is conditional on the stated p-value ranges, not a tail proof. -/
theorem nested_significance_reading (p₁ p₂ p₃ p₄ : ℝ)
    (h₁ : p₁ < 0.01) (h₂ : 0.01 < p₂ ∧ p₂ < 0.05)
    (h₃ : 0.01 < p₃ ∧ p₃ < 0.05) (h₄ : 0.01 < p₄ ∧ p₄ < 0.05) :
    p₁ < 0.05 ∧ p₂ < 0.10 ∧ p₃ < 0.10 ∧ ¬ p₄ < 0.01 := by
  constructor; linarith
  constructor; linarith
  constructor; linarith
  linarith

/-- P041-T11(P1), the three nondetections in p. 5/8: throughout their
printed S6 C rectangles, the pooled, living and deceased |z| are below 1.
This proves the finite Wald part, not the quoted decimal p-values. -/
theorem former_subgroup_nondetections :
    (∀ h s : ℝ, printedInterval 0.691 h → printedInterval 0.318 s → |hazardWald h s| < 1) ∧
    (∀ h s : ℝ, printedInterval 0.775 h → printedInterval 0.503 s → |hazardWald h s| < 1) ∧
    (∀ h s : ℝ, printedInterval 0.627 h → printedInterval 0.406 s → |hazardWald h s| < 1) := by
  refine ⟨fun h s hh hs => (corrected_former_nondetection h s hh hs).2.2, ?_, ?_⟩
  · intro h s hh hs
    exact lt_trans (wald_living_rounding h s hh hs).2 (by norm_num)
  · intro h s hh hs
    exact lt_trans (wald_deceased_rounding h s hh hs).2 (by norm_num)


end AronowAudit.P041

