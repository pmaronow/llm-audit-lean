import AronowAudit.P023.Wave1.Lib.HarmonicTailTailC
import AronowAudit.P023.Wave1.Lib.AbsoluteCosineTailC

/-! Quantitative L1 comparisons, including the origin and the full positive half interval. -/
namespace AronowAudit.P023.Wave1
noncomputable section
open MeasureTheory Set Filter Polynomial
open scoped Topology BigOperators ENNReal
set_option maxHeartbeats 600000

/-- The nonconstant part of the actual projection is odd. -/
theorem tc11_projection_reflection (J : ℕ) (x : ℝ) :
    (projection uniformMargins J).eval (-x) = 1-(projection uniformMargins J).eval x := by
  simp only [tc04_uniform_projection_expansion, tc04_uniform_candidate, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul]
  have hs : (∑ m ∈ Finset.range ((J+1)/2), tc04_odd_coefficient m *
      (AronowAudit.Literature.legendreRodrigues (2*m+1)).eval (-x)) =
      -(∑ m ∈ Finset.range ((J+1)/2), tc04_odd_coefficient m *
      (AronowAudit.Literature.legendreRodrigues (2*m+1)).eval x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [tc04_legendre_parity]
    simp [pow_add, pow_mul]
  rw [hs]
  ring

theorem tc11_residual_abs_even (J : ℕ) (x : ℝ) :
    |popResidual uniformMargins J (-x)| = |popResidual uniformMargins J x| := by
  by_cases hx : x=0
  · simp [hx]
  have he : party (-x) = 1-party x := by
    rcases lt_or_gt_of_ne hx with hn | hp
    · simp [party, not_le.mpr hn, (neg_pos.mpr hn).le]
    · simp [party, hp.le, not_le.mpr (neg_neg_of_pos hp)]
  simp only [popResidual, tc11_projection_reflection, he]
  have h : 1-party x-(1-(projection uniformMargins J).eval x) =
      -(party x-(projection uniformMargins J).eval x) := by ring
  rw [h,abs_neg]

/-- Symmetry exactly cancels the uniform law's factor `1/2`. -/
theorem tc11_residual_positive_half (J : ℕ) :
    expectation uniformMargins (fun x => |popResidual uniformMargins J x|) =
      ∫ x in (0 : ℝ)..1, |popResidual uniformMargins J x| := by
  have hi : IntervalIntegrable (fun x => |popResidual uniformMargins J x|) volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact (tc09_residual_volume_integrable J).abs
  have hn : (∫ x in (-1 : ℝ)..0, |popResidual uniformMargins J x|) =
      ∫ x in (0 : ℝ)..1, |popResidual uniformMargins J x| := by
    simpa only [tc11_residual_abs_even, neg_zero, neg_neg] using
      (intervalIntegral.integral_comp_neg (f:=fun x => |popResidual uniformMargins J x|)
        (a:=(0 : ℝ)) (b:=1)).symm
  rw [tc04_eq_interval]
  have hin : IntervalIntegrable (fun x => |popResidual uniformMargins J x|) volume (-1) 0 :=
    hi.mono_set (by
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0), uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      intro x hx
      exact ⟨hx.1,by linarith [hx.2]⟩)
  have hip : IntervalIntegrable (fun x => |popResidual uniformMargins J x|) volume 0 1 :=
    hi.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      intro x hx
      exact ⟨by linarith [hx.1],hx.2⟩)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hin hip
  rw [← hadd,hn]
  ring

/-- A unit-scale Young inequality suffices to control the interval omitted at the origin. -/
theorem tc11_residual_small_interval (J : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..s, |popResidual uniformMargins J x|) ≤
      2*residualVariance uniformMargins J+s := by
  have hsub : Icc (0 : ℝ) s ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1],hx.2.trans hs.2⟩
  have hsq : IntegrableOn (fun x => popResidual uniformMargins J x^2) (Icc (-1 : ℝ) 1) := by
    exact (integrable_smul_measure (by norm_num : (1/2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (1/2 : ℝ≥0∞) ≠ ⊤)).mp (tc09_residual_square_integrable J)
  have hfullabs : IntegrableOn (fun x => |popResidual uniformMargins J x|) (Icc (-1 : ℝ) 1) volume :=
    (tc09_residual_volume_integrable J).abs
  have habs := hfullabs.mono_set hsub
  have hloc := hsq.mono_set hsub
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (0 : ℝ) s) volume :=
    integrableOn_const (by simp)
  have hle : (∫ x in Icc (0 : ℝ) s, |popResidual uniformMargins J x|) ≤
      (∫ x in Icc (0 : ℝ) s, popResidual uniformMargins J x^2) + s := by
    have h := setIntegral_mono_on habs (hloc.add hconst)
      measurableSet_Icc (fun x _ => by
        change |popResidual uniformMargins J x| ≤ popResidual uniformMargins J x^2+1
        nlinarith [sq_nonneg (|popResidual uniformMargins J x|-1),
          sq_abs (popResidual uniformMargins J x)])
    change (∫ x in Icc (0 : ℝ) s, |popResidual uniformMargins J x|) ≤
      ∫ x in Icc (0 : ℝ) s, popResidual uniformMargins J x^2+1 at h
    rw [integral_add hloc hconst, integral_const] at h
    simpa [Measure.real, Real.volume_Icc, hs.1, smul_eq_mul] using h
  have hfull : (∫ x in Icc (0 : ℝ) s, popResidual uniformMargins J x^2) ≤
      2*residualVariance uniformMargins J := by
    have h := setIntegral_mono_set hsq (Eventually.of_forall fun x => sq_nonneg
      (popResidual uniformMargins J x)) (Eventually.of_forall hsub)
    have he : (∫ x in Icc (-1 : ℝ) 1, popResidual uniformMargins J x^2) =
        2*residualVariance uniformMargins J := by
      unfold residualVariance expectation uniformMargins
      rw [integral_smul_measure]
      norm_num
      ring
    exact h.trans_eq he
  rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
  linarith

/-- The trigonometric Jacobian weight differs from `1/t` by a uniformly bounded quantity. -/
theorem tc11_weight_difference {t : ℝ} (ht : 0 < t) (htp : t < Real.pi/2) :
    |Real.sqrt (Real.cos t)/Real.sin t - 1/t| ≤ Real.pi^2 := by
  have hc : 0 < Real.cos t := tc08_cos_pos ⟨by linarith [Real.pi_pos],htp⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have hr := Real.sqrt_nonneg (Real.cos t)
  have hr2 := Real.sq_sqrt hc.le
  have hr1 : Real.sqrt (Real.cos t) ≤ 1 := Real.sqrt_le_one.mpr (Real.cos_le_one t)
  have hcr : Real.cos t ≤ Real.sqrt (Real.cos t) := by nlinarith
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=t)
  have hsin := Real.sin_le ht.le
  have hsin3 := Real.sin_ge_sub_cube ht.le
  have hsl := Real.mul_le_sin ht.le htp.le
  have hsl' : 2*t ≤ Real.pi*Real.sin t := by
    have h := mul_le_mul_of_nonneg_left hsl Real.pi_pos.le
    field_simp at h
    nlinarith
  have hnum : |t*Real.sqrt (Real.cos t)-Real.sin t| ≤ t^3/2 := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hcr ht.le,
        mul_le_mul_of_nonneg_left hcos ht.le]
    · nlinarith [mul_le_mul_of_nonneg_left hr1 ht.le]
  have hsize : t^3/2 ≤ Real.pi^2*(t*Real.sin t) := by
    have h := mul_le_mul_of_nonneg_left hsl' (mul_nonneg Real.pi_pos.le ht.le)
    have h' := mul_nonneg (by linarith [htp] : 0 ≤ 4*Real.pi-t) (sq_nonneg t)
    nlinarith
  have he : Real.sqrt (Real.cos t)/Real.sin t-1/t =
      (t*Real.sqrt (Real.cos t)-Real.sin t)/(t*Real.sin t) := by field_simp
  rw [he,abs_div,abs_of_pos (mul_pos ht hs)]
  exact (div_le_iff₀ (mul_pos ht hs)).mpr (hnum.trans hsize)

def tc11_leadingDensity (n : ℕ) (t : ℝ) : ℝ :=
  |Real.cos ((2*(n : ℝ)+1/2)*t)| / (2*Real.pi*(n : ℝ)*t)

/-- Comparison with the exact leading absolute cosine density, uniformly up to either endpoint. -/
theorem tc11_density_error (n : ℕ) (hn : 1 ≤ n) {t : ℝ}
    (ht : 0 < t) (htp : t < Real.pi/2) :
    abs (|popResidual uniformMargins (2*n-1) (Real.sin t)| *Real.cos t - tc11_leadingDensity n t) ≤
      |popResidual uniformMargins (2*n-1) (Real.sin t) -
        tc09_harmonicTail n t/(Real.pi*Real.sqrt (Real.cos t))| *Real.cos t +
        (Real.pi/(n : ℝ)^2)*(1/t^2) + Real.pi/(n : ℝ) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : 0 < Real.cos t := tc08_cos_pos ⟨by linarith [Real.pi_pos],htp⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have hr : 0 < Real.sqrt (Real.cos t) := Real.sqrt_pos.mpr hc
  have hr2 := Real.sq_sqrt hc.le
  have hr1 : Real.sqrt (Real.cos t) ≤ 1 := Real.sqrt_le_one.mpr (Real.cos_le_one t)
  let r := popResidual uniformMargins (2*n-1) (Real.sin t)
  let f := tc09_harmonicTail n t
  let c := Real.cos ((2*(n : ℝ)+1/2)*t)
  let A := |f/(Real.pi*Real.sqrt (Real.cos t))| *Real.cos t
  let B := |c| *Real.sqrt (Real.cos t)/(2*Real.pi*(n : ℝ)*Real.sin t)
  have hRA : abs (|r| *Real.cos t-A) ≤
      |r-f/(Real.pi*Real.sqrt (Real.cos t))| *Real.cos t := by
    dsimp [A]
    rw [← sub_mul,abs_mul,abs_of_pos hc]
    exact mul_le_mul_of_nonneg_right (abs_abs_sub_abs_le_abs_sub _ _) hc.le
  have hAB : |A-B| ≤ (Real.pi/(n : ℝ)^2)*(1/t^2) := by
    have hab := tc09_harmonic_tail_bound n hn hs
    have he : A-B = (Real.sqrt (Real.cos t)/Real.pi)*
        (|f|-|c/(2*(n : ℝ)*Real.sin t)|) := by
      dsimp [A,B]
      rw [abs_div,abs_of_pos (mul_pos Real.pi_pos hr),abs_div,
        abs_of_pos (by positivity : 0 < 2*(n : ℝ)*Real.sin t)]
      field_simp
      rw [hr2]
      ring
    rw [he,abs_mul,abs_of_pos (by positivity : 0 < Real.sqrt (Real.cos t)/Real.pi)]
    calc
      _ ≤ (Real.sqrt (Real.cos t)/Real.pi)*(1/((n : ℝ)^2*Real.sin t^2)) :=
        mul_le_mul_of_nonneg_left ((abs_abs_sub_abs_le_abs_sub _ _).trans hab) (by positivity)
      _ ≤ (1/Real.pi)*(1/((n : ℝ)^2*Real.sin t^2)) := by gcongr
      _ ≤ _ := by
        have hsl := Real.mul_le_sin ht.le htp.le
        have hsl' : 2*t ≤ Real.pi*Real.sin t := by
          have h := mul_le_mul_of_nonneg_left hsl Real.pi_pos.le
          field_simp at h
          nlinarith
        calc
          _ = 1/(Real.pi*(n : ℝ)^2*Real.sin t^2) := by ring
          _ ≤ Real.pi/((n : ℝ)^2*t^2) := by
            apply (div_le_div_iff₀ (by positivity : 0 < Real.pi*(n : ℝ)^2*Real.sin t^2)
              (by positivity : 0 < (n : ℝ)^2*t^2)).mpr
            have hsq : t^2 ≤ (Real.pi*Real.sin t)^2 := by
              have h := mul_self_le_mul_self (by positivity : 0 ≤ 2*t) hsl'
              nlinarith
            have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg (n : ℝ))
            nlinarith
          _ = _ := by ring
  have hBD : |B-tc11_leadingDensity n t| ≤ Real.pi/(n : ℝ) := by
    have he : B-tc11_leadingDensity n t =
        (|c|/(2*Real.pi*(n : ℝ))) * (Real.sqrt (Real.cos t)/Real.sin t-1/t) := by
      dsimp [B,tc11_leadingDensity,c]
      ring
    rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ |c|/(2*Real.pi*(n : ℝ)))]
    calc
      _ ≤ (1/(2*Real.pi*(n : ℝ)))*Real.pi^2 := by
        gcongr
        · exact Real.abs_cos_le_one _
        · exact tc11_weight_difference ht htp
      _ ≤ _ := by field_simp; nlinarith [Real.pi_pos]
  have h := (abs_sub_le (|r| *Real.cos t) A (tc11_leadingDensity n t)).trans
    (add_le_add hRA ((abs_sub_le A B _).trans (add_le_add hAB hBD)))
  dsimp [r,f] at h
  linarith

end
end AronowAudit.P023.Wave1
