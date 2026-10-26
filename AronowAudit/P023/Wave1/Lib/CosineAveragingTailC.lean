import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! A fixed-interior oscillatory integral estimate sufficient for divergence. -/

namespace AronowAudit.P023.Wave1
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem tc09_oscillatory_integral_bound {a b k : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hk : 0 < k) :
    |∫ t in a..b, Real.cos (k*t) / t| ≤
      (2/a + (b-a)/a^2) / k := by
  have hb : 0 < b := ha.trans_le hab
  have hdom : ∀ t ∈ Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
  have hc : ContinuousOn (fun t => Real.cos (k*t) / t) (Icc a b) := by
    apply ContinuousOn.div (by fun_prop) continuousOn_id
    exact fun t ht => (hdom t ht).ne'
  have hs : ContinuousOn (fun t => Real.sin (k*t) / t^2) (Icc a b) := by
    apply ContinuousOn.div (by fun_prop) (continuousOn_id.pow 2)
    exact fun t ht => pow_ne_zero 2 (hdom t ht).ne'
  have hd : ∀ t ∈ Icc a b, HasDerivAt (fun t => Real.sin (k*t)/t)
      (k * (Real.cos (k*t)/t) - Real.sin (k*t)/t^2) t := by
    intro t ht
    have h := (((hasDerivAt_id t).const_mul k).sin).div (hasDerivAt_id t) (hdom t ht).ne'
    simp only [id_eq] at h
    convert h using 1
    · rfl
    · field_simp <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (fun t ht => hd t (by simpa only [uIcc_of_le hab] using ht))
    (((hc.const_mul k).sub hs).intervalIntegrable_of_Icc hab)
  rw [intervalIntegral.integral_sub ((hc.const_mul k).intervalIntegrable_of_Icc hab)
    (hs.intervalIntegrable_of_Icc hab), intervalIntegral.integral_const_mul] at hi
  have hsin : |∫ t in a..b, Real.sin (k*t)/t^2| ≤ (b-a)/a^2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := 1/a^2) (f := fun t => Real.sin (k*t)/t^2) ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h
      exact h.trans_eq (by ring)
    · intro t ht
      rw [uIoc_of_le hab] at ht
      have htpos : 0 < t := ha.trans ht.1
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
      calc
        _ ≤ 1/t^2 := div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (sq_nonneg t)
        _ ≤ 1/a^2 := div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ha)
          (by nlinarith [ht.1])
  have hba : |Real.sin (k*b)/b| ≤ 1/a := by
    rw [abs_div, abs_of_pos hb]
    exact (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hb.le).trans
      (one_div_le_one_div_of_le ha hab)
  have haa : |Real.sin (k*a)/a| ≤ 1/a := by
    rw [abs_div, abs_of_pos ha]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) ha.le
  have he : k * (∫ t in a..b, Real.cos (k*t)/t) =
      Real.sin (k*b)/b - Real.sin (k*a)/a + ∫ t in a..b, Real.sin (k*t)/t^2 := by
    linarith
  have hnorm : k * |∫ t in a..b, Real.cos (k*t)/t| ≤ 2/a + (b-a)/a^2 := by
    calc
      _ = |k * (∫ t in a..b, Real.cos (k*t)/t)| := by rw [abs_mul, abs_of_pos hk]
      _ = _ := congrArg abs he
      _ ≤ |Real.sin (k*b)/b - Real.sin (k*a)/a| +
          |∫ t in a..b, Real.sin (k*t)/t^2| := abs_add_le _ _
      _ ≤ (|Real.sin (k*b)/b| + |Real.sin (k*a)/a|) +
          |∫ t in a..b, Real.sin (k*t)/t^2| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ (1/a + 1/a) + (b-a)/a^2 := add_le_add (add_le_add hba haa) hsin
      _ = _ := by ring
  exact (le_div_iff₀ hk).mpr (by simpa only [mul_comm] using hnorm)

theorem tc09_oscillatory_integral_zero {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => ∫ t in a..b, Real.cos ((4*(n : ℝ)+1)*t)/t) atTop (𝓝 0) := by
  have hfreq : Tendsto (fun n : ℕ => 4*(n : ℝ)+1) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro n
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hlim : Tendsto (fun n : ℕ => (2/a+(b-a)/a^2)/(4*(n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hfreq
  apply squeeze_zero_norm (fun n => ?_) hlim
  simpa only [Real.norm_eq_abs] using tc09_oscillatory_integral_bound ha hab
    (show 0 < 4*(n : ℝ)+1 by positivity)

/-- Only a positive logarithmic mean is needed; squaring the cosine suffices. -/
theorem tc09_cosine_square_log_limit {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => ∫ t in a..b, Real.cos ((2*(n : ℝ)+1/2)*t)^2/t) atTop
      (𝓝 (Real.log (b/a)/2)) := by
  have hb : 0 < b := ha.trans_le hab
  have he (n : ℕ) : (∫ t in a..b, Real.cos ((2*(n : ℝ)+1/2)*t)^2/t) =
      (Real.log (b/a) + ∫ t in a..b, Real.cos ((4*(n : ℝ)+1)*t)/t)/2 := by
    have hcont : ContinuousOn (fun t => Real.cos ((4*(n : ℝ)+1)*t)/t) (Icc a b) := by
      apply ContinuousOn.div (by fun_prop) continuousOn_id
      exact fun t ht => (ha.trans_le ht.1).ne'
    have hinv : IntervalIntegrable (fun t : ℝ => 1/t) volume a b :=
      (continuousOn_const.div continuousOn_id
        (fun t ht => (ha.trans_le ht.1).ne')).intervalIntegrable_of_Icc hab
    calc
      _ = ∫ t in a..b, ((1/t) + Real.cos ((4*(n : ℝ)+1)*t)/t)/2 := by
        apply intervalIntegral.integral_congr
        intro t _
        have h := Real.cos_two_mul ((2*(n : ℝ)+1/2)*t)
        rw [show 2*((2*(n : ℝ)+1/2)*t) = (4*(n : ℝ)+1)*t by ring] at h
        linear_combination -h/(2*t)
      _ = _ := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add hinv
          (hcont.intervalIntegrable_of_Icc hab), integral_one_div_of_pos ha hb]
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log (b/a)) atTop (𝓝 _)).add
    (tc09_oscillatory_integral_zero ha hab)).div_const 2
  simpa only [add_zero, ← he] using h

end
end AronowAudit.P023.Wave1
