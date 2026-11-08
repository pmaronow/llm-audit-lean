import SAP.P037a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter SAP.P037a.Bridge
open scoped BigOperators ENNReal NNReal Classical Topology

namespace SAP.P037a.WH.W1.P.T3_L3

open SAP.P037a.WH.W1

theorem expTaylor_half_eq_sum (d : ℕ) (t : ℝ) :
    expTaylor d (t ^ 2 / 2) =
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℝ) ^ k * t ^ (2 * k) / ((2 : ℝ) ^ k * k.factorial) := by
  unfold expTaylor
  apply Finset.sum_congr rfl
  intro k hk
  have hpow : (t ^ 2) ^ k = t ^ (2 * k) := by rw [← pow_mul]
  rw [neg_pow, div_pow, hpow]
  ring

theorem integral_expTaylor_half (d : ℕ) (z : ℝ) :
    ∫ t : ℝ in (0 : ℝ)..z, expTaylor d (t ^ 2 / 2) =
      gaussianTaylorIntegral d z := by
  simp_rw [expTaylor_half_eq_sum]
  have hi : ∀ k ∈ Finset.range (d + 1),
      IntervalIntegrable
        (fun t : ℝ => (-1 : ℝ) ^ k * t ^ (2 * k) /
          ((2 : ℝ) ^ k * k.factorial)) volume 0 z := by
    intro k hk
    apply (show Continuous (fun t : ℝ => (-1 : ℝ) ^ k * t ^ (2 * k) /
      ((2 : ℝ) ^ k * k.factorial)) from by fun_prop).intervalIntegrable
  rw [intervalIntegral.integral_finsetSum hi]
  unfold gaussianTaylorIntegral
  apply Finset.sum_congr rfl
  intro k hk
  simp only [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    integral_pow]
  simp
  field_simp

theorem taylor_integral_bounds (h2 : T3_L2) (z : ℝ) (hz : 0 ≤ z) :
    gaussianTaylorIntegral 25 z ≤
        ∫ t : ℝ in (0 : ℝ)..z, Real.exp (-(t ^ 2 / 2)) ∧
      (∫ t : ℝ in (0 : ℝ)..z, Real.exp (-(t ^ 2 / 2)) : ℝ) ≤
        gaussianTaylorIntegral 24 z := by
  have hpoly25c : Continuous (fun t : ℝ => expTaylor 25 (t ^ 2 / 2)) := by
    unfold expTaylor
    fun_prop
  have hpoly24c : Continuous (fun t : ℝ => expTaylor 24 (t ^ 2 / 2)) := by
    unfold expTaylor
    fun_prop
  have hexpc : Continuous (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) := by
    fun_prop
  have hpoly25i := hpoly25c.intervalIntegrable (μ := volume) (0 : ℝ) z
  have hpoly24i := hpoly24c.intervalIntegrable (μ := volume) (0 : ℝ) z
  have hexpi := hexpc.intervalIntegrable (μ := volume) (0 : ℝ) z
  have hlo : (∫ t : ℝ in (0 : ℝ)..z, expTaylor 25 (t ^ 2 / 2)) ≤
      ∫ t : ℝ in (0 : ℝ)..z, Real.exp (-(t ^ 2 / 2)) := by
    apply intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := z) hz hpoly25i hexpi
    intro t _
    have h := (h2 (t ^ 2 / 2) (by positivity)).1
    simpa using h
  have hhi : (∫ t : ℝ in (0 : ℝ)..z, Real.exp (-(t ^ 2 / 2))) ≤
      ∫ t : ℝ in (0 : ℝ)..z, expTaylor 24 (t ^ 2 / 2) := by
    apply intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := z) hz hexpi hpoly24i
    intro t ht
    have h := (h2 (t ^ 2 / 2) (by positivity)).2
    simpa using h
  rw [← integral_expTaylor_half 25 z, ← integral_expTaylor_half 24 z]
  exact ⟨hlo, hhi⟩

end SAP.P037a.WH.W1.P.T3_L3

open SAP.P037a.WH.W1.P.T3_L3

theorem SAP.P037a.WH.W1.T3_L3_proof : SAP.P037a.WH.W1.T3_L3 := by
  intro h1 h2 z hz
  have hi := taylor_integral_bounds h2 z hz
  have hc : 0 < (1 / Real.sqrt (2 * Real.pi) : ℝ) := by positivity
  have hscaled24 := mul_le_mul_of_nonneg_left hi.2 hc.le
  have hscaled25 := mul_le_mul_of_nonneg_left hi.1 hc.le
  have hcdf := h1 z hz
  have htail : wholeNormalTail z =
      1 - 2 * (1 / Real.sqrt (2 * Real.pi)) *
        (∫ t : ℝ in (0 : ℝ)..z, Real.exp (-(t ^ 2 / 2))) := by
    rw [wholeNormalTail, hcdf]
    ring
  constructor
  · rw [htail]
    have hcoeff : 2 * gaussianTaylorIntegral 24 z / Real.sqrt (2 * Real.pi) =
        2 * (1 / Real.sqrt (2 * Real.pi)) * gaussianTaylorIntegral 24 z := by ring
    rw [hcoeff]
    nlinarith [hscaled24]
  · rw [htail]
    have hcoeff : 2 * gaussianTaylorIntegral 25 z / Real.sqrt (2 * Real.pi) =
        2 * (1 / Real.sqrt (2 * Real.pi)) * gaussianTaylorIntegral 25 z := by ring
    rw [hcoeff]
    nlinarith [hscaled25]

