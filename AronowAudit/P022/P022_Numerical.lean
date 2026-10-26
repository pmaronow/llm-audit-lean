import Mathlib

namespace AronowAudit.P022

open scoped BigOperators

noncomputable section

/-- A number "displays as" a three-decimal value when it is within 1/2000,
including both tie endpoints. Table 1, p. 857; P022-N003. -/
def displaysThree (x p : ℝ) : Prop := p - 1 / 2000 ≤ x ∧ x ≤ p + 1 / 2000

/-- The half-width of a printed confidence interval is (U-L)/2.
Table 1, p. 857. -/
def halfWidth (L U : ℝ) : ℝ := (U - L) / 2

/-- Percentage reduction in nominal variance: 100(1-VH/Va).
Section 6, p. 857. -/
def reductionPercent (Va VH : ℝ) : ℝ := 100 * (1 - VH / Va)

/-- Finite lemma for P022-T11: closed endpoint rounding bins give the
half-width bin, Table 1, p. 857. -/
theorem half_width_rounding (L U l u : ℝ)
    (hL : displaysThree L l) (hU : displaysThree U u) :
    (u - l) / 2 - 1 / 2000 ≤ halfWidth L U ∧
    halfWidth L U ≤ (u - l) / 2 + 1 / 2000 := by
  unfold displaysThree at hL hU
  unfold halfWidth
  constructor <;> linarith [hL.1, hL.2, hU.1, hU.2]

/-- Finite lemma for P022-T11: the rounded interval columns force
(h/a)^2 ≥ 178929/190969. Table 1, p. 857. -/
theorem table1_ratio_lower_bound (a h : ℝ)
    (ha : 0 < a) (ha_max : a ≤ (437 / 500 : ℝ))
    (hh_min : (423 / 500 : ℝ) ≤ h) :
    (178929 / 190969 : ℝ) ≤ (h / a) ^ 2 := by
  have ha_sq : a ^ 2 ≤ (190969 / 250000 : ℝ) := by
    have hx := mul_nonneg (sub_nonneg.mpr ha_max)
      (show (0 : ℝ) ≤ 437 / 500 + a by linarith)
    nlinarith
  have hh_sq : (178929 / 250000 : ℝ) ≤ h ^ 2 := by
    have hx := mul_nonneg (sub_nonneg.mpr hh_min)
      (show (0 : ℝ) ≤ h + 423 / 500 by linarith)
    nlinarith
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos ha)).2
  nlinarith

/-- P022-T11, corrected numerical claim: under closed rounding bins for
both Table 1 columns and a common positive Wald multiplier, the reduction
lies between 2400/397 and 1204000/190969, strictly between 5.5 and 6.5.
Section 6 and Table 1, p. 857. -/
theorem table1_corrected_reduction (Va VH z L U LH UH : ℝ)
    (hVa : 0 < Va) (hVH : 0 < VH) (hz : 0 < z)
    (hL : displaysThree L (-1555 / 1000))
    (hU : displaysThree U (192 / 1000))
    (hLH : displaysThree LH (-1528 / 1000))
    (hUH : displaysThree UH (165 / 1000))
    (haW : halfWidth L U = z * Real.sqrt Va)
    (hhW : halfWidth LH UH = z * Real.sqrt VH)
    (hVaBin : displaysThree Va (199 / 1000))
    (hVHBin : displaysThree VH (186 / 1000)) :
    (2400 / 397 : ℝ) ≤ reductionPercent Va VH ∧
    reductionPercent Va VH ≤ (1204000 / 190969 : ℝ) ∧
    (11 / 2 : ℝ) < reductionPercent Va VH ∧
    reductionPercent Va VH < (13 / 2 : ℝ) := by
  have haBin := half_width_rounding L U _ _ hL hU
  have hhBin := half_width_rounding LH UH _ _ hLH hUH
  have ha : 0 < halfWidth L U := by linarith [haBin.1]
  have haMax : halfWidth L U ≤ (437 / 500 : ℝ) := by linarith [haBin.2]
  have hhMin : (423 / 500 : ℝ) ≤ halfWidth LH UH := by linarith [hhBin.1]
  have haSq : (halfWidth L U) ^ 2 = z ^ 2 * Va := by
    rw [haW, mul_pow, Real.sq_sqrt hVa.le]
  have hhSq : (halfWidth LH UH) ^ 2 = z ^ 2 * VH := by
    rw [hhW, mul_pow, Real.sq_sqrt hVH.le]
  have hRatio : VH / Va = (halfWidth LH UH / halfWidth L U) ^ 2 := by
    rw [div_pow, haSq, hhSq]
    field_simp
  have hRatioLow := table1_ratio_lower_bound _ _ ha haMax hhMin
  rw [← hRatio] at hRatioLow
  have hRatioUp : VH / Va ≤ (373 / 397 : ℝ) := by
    apply (div_le_iff₀ hVa).2
    unfold displaysThree at hVaBin hVHBin
    linarith [hVaBin.1, hVHBin.2]
  unfold reductionPercent
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- P022-T11(c): treating the displayed variance entries as exact gives
1300/199 percent, explaining the separate rounded-input calculation.
This does not assert the unrounded empirical reduction. Table 1, p. 857. -/
theorem displayed_variance_reduction :
    reductionPercent (199 / 1000) (186 / 1000) = (1300 / 199 : ℝ) := by
  norm_num [reductionPercent]

/-- P022-T12(b), finite Cauchy-Schwarz lemma: the squared average square
root of nonnegative variances is at most their average. Section 6.1, p. 858. -/
theorem finite_sqrt_mean_squared_le_mean {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (v : ι → ℝ) (hv : ∀ i ∈ s, 0 ≤ v i) :
    (𝔼 i ∈ s, Real.sqrt (v i)) ^ 2 ≤ 𝔼 i ∈ s, v i := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (v i)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.expect_const hs] at h
  have hsq : (𝔼 i ∈ s, Real.sqrt (v i) ^ 2) = 𝔼 i ∈ s, v i :=
    Finset.expect_congr rfl (fun i hi => Real.sq_sqrt (hv i hi))
  rw [hsq] at h
  simpa using h

/-- P022-T12(b): for every nonempty finite simulation collection, squared
mean Wald width is at most c^2 times mean variance. Section 6.1, p. 858.
The average is over the realized collection, not a population expectation. -/
theorem finite_wald_mean_width_squared_le {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (v : ι → ℝ) (hv : ∀ i ∈ s, 0 ≤ v i) (c : ℝ) :
    (𝔼 i ∈ s, c * Real.sqrt (v i)) ^ 2 ≤ c ^ 2 * (𝔼 i ∈ s, v i) := by
  rw [← Finset.mul_expect]
  have h := mul_le_mul_of_nonneg_left
    (finite_sqrt_mean_squared_le_mean s hs v hv) (sq_nonneg c)
  simpa only [mul_pow] using h

/-- P022-T12(c): the rounded Neyman row in Table 1 bounds the common
squared full-width multiplier without evaluating a normal quantile. p. 857. -/
theorem table1_multiplier_bound (c q d : ℝ)
    (hq : 391 / 2000 ≤ q) (hd0 : 0 ≤ d) (hd : d ≤ 867 / 500)
    (hwidth : d ^ 2 = c ^ 2 * q) :
    c ^ 2 ≤ 44217 / 2875 := by
  have hdsq : d ^ 2 ≤ (867 / 500 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (d - 867 / 500)]
  have hprod : (391 / 2000 : ℝ) * c ^ 2 ≤ c ^ 2 * q := by
    have h := mul_nonneg (sub_nonneg.mpr hq) (sq_nonneg c)
    nlinarith
  nlinarith

/-- P022-T12(d): the Table 2 width, true variance, and quoted -0.007 bias
cannot summarize the same finite collection with the Table 1 multiplier.
Section 6.1, p. 858; closed bins allow every nearest-rounding tie rule. -/
theorem reported_numbers_incompatible (c meanWidth meanVariance trueVariance bias : ℝ)
    (hc : c ^ 2 ≤ 44217 / 2875)
    (hmu : 0 ≤ meanVariance)
    (hw : 3447 / 2000 ≤ meanWidth)
    (hcs : meanWidth ^ 2 ≤ c ^ 2 * meanVariance)
    (ht : trueVariance ≤ 399 / 2000)
    (hb : bias ≤ -(13 / 2000))
    (hdef : meanVariance = trueVariance + bias) : False := by
  have hmuCap : meanVariance ≤ 193 / 1000 := by linarith
  have hwSq : (3447 / 2000 : ℝ) ^ 2 ≤ meanWidth ^ 2 := by
    nlinarith [sq_nonneg (meanWidth - 3447 / 2000)]
  have hprod : c ^ 2 * meanVariance ≤ (44217 / 2875 : ℝ) * meanVariance := by
    have h := mul_nonneg (sub_nonneg.mpr hc) hmu
    nlinarith
  have hcap : c ^ 2 * meanVariance ≤ (44217 / 2875 : ℝ) * (193 / 1000) := by
    nlinarith
  nlinarith

/-- P022-T12(e): with full-width multiplier 3.92 the width column forces
mean variance ≥ 11881809/61465600 > 0.193. Table 2, p. 858. -/
theorem fixed_multiplier_mean_lower (w v : ℝ)
    (hw : 3447 / 2000 ≤ w) (h : w ^ 2 ≤ (98 / 25 : ℝ) ^ 2 * v) :
    (11881809 / 61465600 : ℝ) ≤ v ∧ (193 / 1000 : ℝ) < v := by
  have hsq : (3447 / 2000 : ℝ) ^ 2 ≤ w ^ 2 := by
    nlinarith [sq_nonneg (w - 3447 / 2000)]
  constructor <;> nlinarith

end
end AronowAudit.P022

