import AronowAudit.P023.Wave1.Lib.CosineAveragingTailC
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded

/-! The exact average of absolute cosine, with a uniform logarithmic integral remainder. -/
namespace AronowAudit.P023.Wave1
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

def tc11_centeredCos (t : ℝ) : ℝ := |Real.cos t| - 2/Real.pi

theorem tc11_centeredCos_continuous : Continuous tc11_centeredCos := by
  unfold tc11_centeredCos
  fun_prop

theorem tc11_centeredCos_periodic : Function.Periodic tc11_centeredCos Real.pi := by
  intro t
  simp [tc11_centeredCos, Real.cos_add_pi]

theorem tc11_centeredCos_mean : (∫ t in (0 : ℝ)..Real.pi, tc11_centeredCos t) = 0 := by
  have hp : Function.Periodic (fun t : ℝ => |Real.cos t|) Real.pi := by
    intro t
    simp [Real.cos_add_pi]
  have he := hp.intervalIntegral_add_eq (0 : ℝ) (-Real.pi/2)
  simp only [zero_add] at he
  have hent : -Real.pi/2+Real.pi = Real.pi/2 := by ring
  rw [hent] at he
  have hab : -Real.pi/2 ≤ Real.pi/2 := by linarith [Real.pi_pos]
  have hcos : (∫ t in (-Real.pi/2)..(Real.pi/2), |Real.cos t|) = 2 := by
    calc
      _ = ∫ t in (-Real.pi/2)..(Real.pi/2), Real.cos t := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hab]
        intro t ht
        exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc (by simpa only [neg_div] using ht))
      _ = 2 := by rw [integral_cos]; norm_num [neg_div]
  unfold tc11_centeredCos
  rw [intervalIntegral.integral_sub (Real.continuous_cos.abs.intervalIntegrable _ _)
    (intervalIntegrable_const), he, hcos, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  field_simp
  ring

def tc11_cosPrimitive (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, tc11_centeredCos u

theorem tc11_cosPrimitive_deriv (t : ℝ) :
    HasDerivAt tc11_cosPrimitive (tc11_centeredCos t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (tc11_centeredCos_continuous.intervalIntegrable _ _)
    tc11_centeredCos_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    tc11_centeredCos_continuous.continuousAt

theorem tc11_cosPrimitive_continuous : Continuous tc11_cosPrimitive :=
  continuous_iff_continuousAt.mpr (fun t => (tc11_cosPrimitive_deriv t).continuousAt)

theorem tc11_cosPrimitive_periodic : Function.Periodic tc11_cosPrimitive Real.pi := by
  intro t
  unfold tc11_cosPrimitive
  rw [tc11_centeredCos_periodic.intervalIntegral_add_eq_add 0 t
    (fun a b => tc11_centeredCos_continuous.intervalIntegrable a b),
    zero_add, tc11_centeredCos_mean, add_zero]

theorem tc11_cosPrimitive_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |tc11_cosPrimitive t| ≤ M := by
  obtain ⟨M,hM,hb⟩ := (tc11_cosPrimitive_periodic.isBounded_of_continuous
    Real.pi_ne_zero tc11_cosPrimitive_continuous).exists_pos_norm_le
  exact ⟨M,hM.le,fun t => by simpa only [Real.norm_eq_abs] using hb _ (mem_range_self t)⟩

theorem tc11_inverse_square_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1/t^2) = 1/a-1/b := by
  have hc : ContinuousOn (fun t : ℝ => 1/t^2) (Icc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (ha.trans_le ht.1).ne')
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=a) (b:=b) (f:=fun t : ℝ => -t⁻¹)
    (f':=fun t : ℝ => 1/t^2)
    (fun t ht => by
      have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
      have hp : t ≠ 0 := (ha.trans_le ht'.1).ne'
      convert (hasDerivAt_inv hp).neg using 1 <;> simp only [Pi.neg_apply, neg_neg, one_div])
    (hc.intervalIntegrable_of_Icc hab)
  convert hi using 1 <;> simp only [one_div] <;> ring

/-- Bounded primitives give the exact `2/pi` mean against the singular weight. -/
theorem tc11_absolute_cosine_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b k : ℝ, 0 < a → a ≤ b → 0 < k →
      |(∫ t in a..b, |Real.cos (k*t)|/t) - (2/Real.pi)*Real.log (b/a)| ≤ C/(k*a) := by
  obtain ⟨M,hM,hbound⟩ := tc11_cosPrimitive_bounded
  refine ⟨2*M,by positivity,?_⟩
  intro a b k ha hab hk
  have hb : 0 < b := ha.trans_le hab
  have hpos : ∀ t ∈ Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
  have hc : ContinuousOn (fun t => tc11_centeredCos (k*t)/t) (Icc a b) :=
    (tc11_centeredCos_continuous.comp (by fun_prop)).continuousOn.div
      continuousOn_id (fun t ht => (hpos t ht).ne')
  have hG : ContinuousOn (fun t => tc11_cosPrimitive (k*t)/t^2) (Icc a b) :=
    (tc11_cosPrimitive_continuous.comp (by fun_prop)).continuousOn.div
      (continuousOn_id.pow 2) (fun t ht => pow_ne_zero 2 (hpos t ht).ne')
  have hinv : ContinuousOn (fun t : ℝ => 1/t^2) (Icc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (hpos t ht).ne')
  have hd : ∀ t ∈ Icc a b, HasDerivAt (fun t => tc11_cosPrimitive (k*t)/t)
      (k*(tc11_centeredCos (k*t)/t) - tc11_cosPrimitive (k*t)/t^2) t := by
    intro t ht
    have h := ((tc11_cosPrimitive_deriv (k*t)).comp t
      ((hasDerivAt_id t).const_mul k)).div (hasDerivAt_id t) (hpos t ht).ne'
    simp only [Function.comp_apply, id_eq, mul_one] at h
    convert h using 1
    · rfl
    · field_simp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=a) (b:=b) (fun t ht => hd t (by simpa only [uIcc_of_le hab] using ht))
    (((hc.const_mul k).sub hG).intervalIntegrable_of_Icc hab)
  rw [intervalIntegral.integral_sub ((hc.const_mul k).intervalIntegrable_of_Icc hab)
    (hG.intervalIntegrable_of_Icc hab), intervalIntegral.integral_const_mul] at hi
  have hGi : |∫ t in a..b, tc11_cosPrimitive (k*t)/t^2| ≤ M*(1/a-1/b) := by
    calc
      _ ≤ ∫ t in a..b, |tc11_cosPrimitive (k*t)/t^2| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in a..b, M*(1/t^2) := by
        apply intervalIntegral.integral_mono_on hab (hG.abs.intervalIntegrable_of_Icc hab)
          ((hinv.const_mul M).intervalIntegrable_of_Icc hab)
        intro t ht
        rw [abs_div, abs_of_nonneg (sq_nonneg t)]
        simpa only [mul_one_div] using div_le_div_of_nonneg_right (hbound (k*t)) (sq_nonneg t)
      _ = _ := by rw [intervalIntegral.integral_const_mul, tc11_inverse_square_integral ha hab]
  have hba : |tc11_cosPrimitive (k*b)/b| ≤ M/b := by
    rw [abs_div, abs_of_pos hb]
    exact div_le_div_of_nonneg_right (hbound (k*b)) hb.le
  have haa : |tc11_cosPrimitive (k*a)/a| ≤ M/a := by
    rw [abs_div, abs_of_pos ha]
    exact div_le_div_of_nonneg_right (hbound (k*a)) ha.le
  have he : k*(∫ t in a..b, tc11_centeredCos (k*t)/t) =
      tc11_cosPrimitive (k*b)/b-tc11_cosPrimitive (k*a)/a +
        ∫ t in a..b, tc11_cosPrimitive (k*t)/t^2 := by linarith
  have hiabs : k*|∫ t in a..b, tc11_centeredCos (k*t)/t| ≤ 2*M/a := by
    calc
      _ = |k*(∫ t in a..b, tc11_centeredCos (k*t)/t)| := by rw [abs_mul,abs_of_pos hk]
      _ = _ := congrArg abs he
      _ ≤ |tc11_cosPrimitive (k*b)/b-tc11_cosPrimitive (k*a)/a| +
          |∫ t in a..b, tc11_cosPrimitive (k*t)/t^2| := abs_add_le _ _
      _ ≤ (M/b+M/a)+M*(1/a-1/b) :=
        add_le_add ((abs_sub _ _).trans (add_le_add hba haa)) hGi
      _ = _ := by ring
  have hident : (∫ t in a..b, tc11_centeredCos (k*t)/t) =
      (∫ t in a..b, |Real.cos (k*t)|/t) - (2/Real.pi)*Real.log (b/a) := by
    simp only [tc11_centeredCos, sub_div]
    have hcosint : IntervalIntegrable (fun t : ℝ => |Real.cos (k*t)|/t) volume a b := by
      apply ContinuousOn.intervalIntegrable_of_Icc hab
      apply ContinuousOn.div (by fun_prop) continuousOn_id
      exact fun t ht => (hpos t ht).ne'
    have hconstint : IntervalIntegrable (fun t : ℝ => (2/Real.pi)/t) volume a b := by
      apply ContinuousOn.intervalIntegrable_of_Icc hab
      exact continuousOn_const.div continuousOn_id (fun t ht => (hpos t ht).ne')
    rw [intervalIntegral.integral_sub hcosint hconstint]
    congr 1
    simp_rw [div_eq_mul_one_div (2/Real.pi)]
    rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos ha hb]
  rw [← hident]
  apply (le_div_iff₀ (mul_pos hk ha)).mpr
  have h := mul_le_mul_of_nonneg_right hiabs ha.le
  have haa : (2*M/a)*a = 2*M := by field_simp
  rw [haa] at h
  nlinarith

end
end AronowAudit.P023.Wave1
