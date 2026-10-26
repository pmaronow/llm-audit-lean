import AronowAudit.P023.Wave1.Lib.LegendreMomentsTailC
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Legendre sine approximation on a moving interior interval

The transformed equation is treated directly. Its normalized energy decreases
on the positive half interval; variation of constants is an exact application
of the fundamental theorem of calculus to a Wronskian.
-/

noncomputable section
open MeasureTheory Set Polynomial
open scoped BigOperators

namespace AronowAudit.P023.Wave1
open AronowAudit.Literature

/-- The classical Legendre equation, in the precise Rodrigues normalization. -/
theorem tc08_legendre_ode (k : ℕ) (x : ℝ) :
    (1-x^2) * (legendreRodrigues k).derivative.derivative.eval x -
      2*x*(legendreRodrigues k).derivative.eval x +
      (k : ℝ)*((k : ℝ)+1)*(legendreRodrigues k).eval x = 0 := by
  let p := legendreRodrigues k
  have hf : Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.jacobiShifted k 0 0 =
      fun y : ℝ => p.eval (1-2*y) := by
    funext y
    rw [Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.jacobiShifted_zero_zero_eq_shiftedLegendre]
    dsimp [p]
    rw [tc04_legendre_shift]
    congr 1
    ring
  have hd : deriv (Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.jacobiShifted k 0 0) =
      fun y : ℝ => p.derivative.eval (1-2*y) * (-2) := by
    rw [hf]
    funext y
    have hi : HasDerivAt (fun z : ℝ => 1-2*z) (-2) y := by
      convert (hasDerivAt_const y (1:ℝ)).sub ((hasDerivAt_id' y).const_mul 2) using 1 <;> norm_num
    exact ((p.hasDerivAt (1-2*y)).comp y hi).deriv
  have hdd : deriv (deriv
      (Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.jacobiShifted k 0 0)) =
      fun y : ℝ => p.derivative.derivative.eval (1-2*y) * 4 := by
    rw [hd]
    funext y
    exact ((((p.derivative.hasDerivAt (1-2*y)).comp y
      ((hasDerivAt_const y 1).sub ((hasDerivAt_id y).const_mul 2))).mul_const (-2)).deriv).trans
        (by ring)
  have h := Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.jacobiShifted_ode
    k 0 0 ((1-x)/2) (by norm_num)
  rw [hdd, hd, hf] at h
  simp only [show 1-2*((1-x)/2)=x by ring, add_zero, zero_add] at h
  change (1-x^2)*p.derivative.derivative.eval x - 2*x*p.derivative.eval x +
    (k : ℝ)*((k : ℝ)+1)*p.eval x = 0
  linear_combination h

/-- The odd polynomial vanishes at the origin. -/
theorem tc08_legendre_odd_zero (m : ℕ) :
    (legendreRodrigues (2*m+1)).eval 0 = 0 := by
  have h := tc04_legendre_parity (2*m+1) 0
  simp only [neg_zero, pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul,
    neg_one_mul] at h
  linarith

/-- Initial slope, obtained by integrating the polynomial differential equation
and using the exact odd half moment. -/
theorem tc08_legendre_odd_derivative_zero (m : ℕ) :
    (legendreRodrigues (2*m+1)).derivative.eval 0 =
      (-1 : ℝ)^m * (2*(m : ℝ)+1)*centralBinomial m := by
  let p := legendreRodrigues (2*m+1)
  let q : Polynomial ℝ := (1-X^2)*p.derivative
  have he (x : ℝ) : q.derivative.eval x =
      -((2*(m : ℝ)+1)*(2*(m : ℝ)+2))*p.eval x := by
    have h := tc08_legendre_ode (2*m+1) x
    dsimp [q]
    simp only [derivative_mul, derivative_sub, derivative_one, derivative_pow,
      derivative_X, mul_one, eval_add, eval_mul, eval_sub, eval_one,
      eval_pow, eval_X, eval_C, eval_zero]
    dsimp [p] at *
    push_cast at h
    linear_combination h
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (fun x _ => q.hasDerivAt x)
    (q.derivative.continuous.intervalIntegrable 0 1)
  simp_rw [he] at hi
  rw [intervalIntegral.integral_const_mul] at hi
  simp only [q, eval_mul, eval_sub, eval_one, eval_pow, eval_X] at hi
  norm_num at hi
  change ((2*(m:ℝ)+1)*(2*(m:ℝ)+2)) *
    (∫ x in (0:ℝ)..1, (legendreRodrigues (2*m+1)).eval x) = _ at hi
  rw [odd_legendre_half_moment] at hi
  have hm : (2*(m:ℝ)+2) ≠ 0 := by positivity
  field_simp at hi
  dsimp [p] at hi
  nlinarith [hi]

/-- The frequency of the odd Legendre equation after the sine substitution. -/
def tc08_frequency (m : ℕ) : ℝ := 2*(m:ℝ)+3/2

/-- The unknown in Liouville normal form. -/
def tc08_u (m : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (Real.cos t) * (legendreRodrigues (2*m+1)).eval (Real.sin t)

/-- An explicit first derivative, also useful without unfolding `deriv`. -/
def tc08_du (m : ℕ) (t : ℝ) : ℝ :=
  -(Real.sin t)/(2*Real.sqrt (Real.cos t)) *
      (legendreRodrigues (2*m+1)).eval (Real.sin t) +
    Real.sqrt (Real.cos t)*Real.cos t *
      (legendreRodrigues (2*m+1)).derivative.eval (Real.sin t)

/-- Positivity of the square-root factor throughout the interval of analysis. -/
theorem tc08_cos_pos {t : ℝ} (ht : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2)) :
    0 < Real.cos t := Real.cos_pos_of_mem_Ioo ht

/-- The exact first derivative in Liouville normal form. -/
theorem tc08_hasDerivAt_u (m : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2)) :
    HasDerivAt (tc08_u m) (tc08_du m t) t := by
  have hc := tc08_cos_pos ht
  have hs := (Real.hasDerivAt_cos t).sqrt hc.ne'
  have hp := ((legendreRodrigues (2*m+1)).hasDerivAt (Real.sin t)).comp t
    (Real.hasDerivAt_sin t)
  convert hs.mul hp using 1
  · rfl
  · dsimp [tc08_du, Function.comp_def]
    ring


/-- The explicit derivative satisfies the transformed differential equation. -/
theorem tc08_hasDerivAt_du (m : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2)) :
    HasDerivAt (tc08_du m)
      (-((tc08_frequency m)^2 + 1/(4*(Real.cos t)^2))*tc08_u m t) t := by
  have hc := tc08_cos_pos ht
  have hr : 0 < Real.sqrt (Real.cos t) := Real.sqrt_pos.2 hc
  have hs := (Real.hasDerivAt_cos t).sqrt hc.ne'
  have hp := ((legendreRodrigues (2*m+1)).hasDerivAt (Real.sin t)).comp t
    (Real.hasDerivAt_sin t)
  have hdp := ((legendreRodrigues (2*m+1)).derivative.hasDerivAt (Real.sin t)).comp t
    (Real.hasDerivAt_sin t)
  have hquot := (Real.hasDerivAt_sin t).neg.div (hs.const_mul 2) (by positivity)
  have hd := (hquot.mul hp).add ((hs.mul (Real.hasDerivAt_cos t)).mul hdp)
  convert hd using 1
  · rfl
  · dsimp [tc08_frequency, tc08_u]
    have ho := tc08_legendre_ode (2*m+1) (Real.sin t)
    push_cast at ho
    have hsc := Real.sin_sq_add_cos_sq t
    have hrc := Real.sq_sqrt hc.le
    field_simp
    ring_nf
    ring_nf at ho hsc hrc
    grind


/-- The positive squared frequency in the transformed equation. -/
def tc08_q (m : ℕ) (t : ℝ) : ℝ :=
  (tc08_frequency m)^2 + 1/(4*(Real.cos t)^2)

/-- The normalized energy (Sonin's function). -/
def tc08_energy (m : ℕ) (t : ℝ) : ℝ :=
  (tc08_u m t)^2 + (tc08_du m t)^2 / tc08_q m t

/-- Differentiation of the squared frequency. -/
theorem tc08_hasDerivAt_q (m : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2)) :
    HasDerivAt (tc08_q m) (Real.sin t/(2*(Real.cos t)^3)) t := by
  have hc := (tc08_cos_pos ht).ne'
  have hd := (hasDerivAt_const t (1:ℝ)).div
    (((Real.hasDerivAt_cos t).pow 2).const_mul 4)
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hc))
  convert (hasDerivAt_const t ((tc08_frequency m)^2)).add hd using 1
  · rfl
  · simp only [Pi.pow_apply, Nat.cast_ofNat, pow_one, Nat.reduceSub, zero_mul, one_mul, zero_add]
    field_simp
    ring

/-- Positivity of the squared frequency. -/
theorem tc08_q_pos (m : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2)) : 0 < tc08_q m t := by
  have hc := tc08_cos_pos ht
  dsimp [tc08_q]
  positivity

/-- The derivative of the normalized energy is nonpositive for positive times. -/
theorem tc08_hasDerivAt_energy (m : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2)) :
    HasDerivAt (tc08_energy m)
      (-(Real.sin t/(2*(Real.cos t)^3))*(tc08_du m t)^2/(tc08_q m t)^2) t := by
  have hq := (tc08_q_pos m ht).ne'
  have hd := ((tc08_hasDerivAt_u m ht).pow 2).add
    (((tc08_hasDerivAt_du m ht).pow 2).div (tc08_hasDerivAt_q m ht) hq)
  convert hd using 1
  · rfl
  · simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    change _ = 2*tc08_u m t*tc08_du m t +
      (2*tc08_du m t*(-(tc08_q m t)*tc08_u m t)*tc08_q m t -
        (tc08_du m t)^2*(Real.sin t/(2*(Real.cos t)^3))) / (tc08_q m t)^2
    field_simp
    ring

/-- The initial slope, including its alternating sign. -/
def tc08_initial (m : ℕ) : ℝ :=
  (-1 : ℝ)^m*(2*(m:ℝ)+1)*centralBinomial m

/-- The frequency is strictly positive, including at degree one. -/
theorem tc08_frequency_pos (m : ℕ) : 0 < tc08_frequency m := by
  dsimp [tc08_frequency]
  positivity

/-- The normalized energy decreases on every compact positive half interval. -/
theorem tc08_energy_antitone (m : ℕ) {T : ℝ} (hT : 0 ≤ T) (hTp : T < Real.pi/2) :
    AntitoneOn (tc08_energy m) (Icc 0 T) := by
  have hdom {s : ℝ} (hs : s ∈ Icc 0 T) :
      s ∈ Ioo (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [Real.pi_pos, hs.1], lt_of_le_of_lt hs.2 hTp⟩
  apply antitoneOn_of_deriv_nonpos (convex_Icc (0:ℝ) T)
  · intro s hs
    exact (tc08_hasDerivAt_energy m (hdom hs)).continuousAt.continuousWithinAt
  · intro s hs
    exact (tc08_hasDerivAt_energy m (hdom (interior_subset hs))).differentiableAt.differentiableWithinAt
  · intro s hs
    have hs' := interior_subset hs
    rw [(tc08_hasDerivAt_energy m (hdom hs')).deriv]
    have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi
      hs'.1 (by linarith [hs'.2])
    have hc := tc08_cos_pos (hdom hs')
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _))
      (sq_nonneg _)

/-- A uniform amplitude bound, valid all the way up to the open endpoint.
No Gronwall estimate or unproved Legendre asymptotic is used. -/
theorem legendre_transformed_amplitude (m : ℕ) {t : ℝ}
    (ht : t ∈ Ico (0:ℝ) (Real.pi/2)) :
    |tc08_u m t| ≤ |tc08_initial m|/tc08_frequency m := by
  have ht0 : (0:ℝ) ∈ Icc 0 t := ⟨le_rfl, ht.1⟩
  have htt : t ∈ Icc (0:ℝ) t := ⟨ht.1, le_rfl⟩
  have he := tc08_energy_antitone m ht.1 ht.2 ht0 htt ht.1
  have h0 : tc08_energy m 0 =
      (tc08_initial m)^2 / ((tc08_frequency m)^2+1/4) := by
    simp [tc08_energy, tc08_q, tc08_u, tc08_du,
      tc08_initial, tc08_legendre_odd_zero, tc08_legendre_odd_derivative_zero]
  rw [h0] at he
  have ht' : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [Real.pi_pos, ht.1], ht.2⟩
  have helo : (tc08_u m t)^2 ≤ tc08_energy m t := by
    dsimp [tc08_energy]
    exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (tc08_q_pos m ht').le)
  have hl := tc08_frequency_pos m
  have hb : (tc08_initial m)^2 / ((tc08_frequency m)^2+1/4) ≤
      (|tc08_initial m|/tc08_frequency m)^2 := by
    rw [div_pow, sq_abs]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hl) (by linarith)
  have hu := helo.trans (he.trans hb)
  exact (sq_le_sq₀ (abs_nonneg _) (div_nonneg (abs_nonneg _) hl.le)).mp
    (by simpa only [sq_abs] using hu)

/-- Exact variation of constants, proved by integrating a Wronskian. -/
theorem legendre_volterra (m : ℕ) {t : ℝ}
    (ht : t ∈ Ico (0:ℝ) (Real.pi/2)) :
    tc08_u m t = tc08_initial m / tc08_frequency m * Real.sin (tc08_frequency m*t) -
      (∫ s in (0:ℝ)..t, Real.sin (tc08_frequency m*(t-s))*tc08_u m s /
        (Real.cos s)^2) / (4*tc08_frequency m) := by
  let L := tc08_frequency m
  let F := fun s : ℝ => Real.sin (L*(t-s))*tc08_u m s/(Real.cos s)^2
  let W := fun s : ℝ => tc08_du m s*Real.sin (L*(t-s)) +
    L*tc08_u m s*Real.cos (L*(t-s))
  have hdom {s : ℝ} (hs : s ∈ Icc (0:ℝ) t) :
      s ∈ Ioo (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [Real.pi_pos, hs.1], lt_of_le_of_lt hs.2 ht.2⟩
  have hF : ContinuousOn F (Icc (0:ℝ) t) := by
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · fun_prop
      · intro s hs
        exact (tc08_hasDerivAt_u m (hdom hs)).continuousAt.continuousWithinAt
    · fun_prop
    · intro s hs
      exact pow_ne_zero _ (tc08_cos_pos (hdom hs)).ne'
  have hW {s : ℝ} (hs : s ∈ Icc (0:ℝ) t) : HasDerivAt W ((-1/4)*F s) s := by
    have ha := ((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul L
    have hd := ((tc08_hasDerivAt_du m (hdom hs)).mul ha.sin).add
      (((tc08_hasDerivAt_u m (hdom hs)).const_mul L).mul ha.cos)
    convert hd using 1
    · rfl
    · dsimp [F, L, tc08_q]
      field_simp
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := t) (fun s hs => hW (by simpa [uIcc_of_le ht.1] using hs))
    ((hF.const_mul (-1/4)).intervalIntegrable_of_Icc ht.1)
  rw [intervalIntegral.integral_const_mul] at hi
  have hW0 : W 0 = tc08_initial m * Real.sin (L*t) := by
    simp [W, tc08_du, tc08_u, tc08_initial, tc08_legendre_odd_derivative_zero,
      tc08_legendre_odd_zero]
  have hWt : W t = L*tc08_u m t := by simp [W]
  rw [hW0, hWt] at hi
  change tc08_u m t = tc08_initial m / L * Real.sin (L*t) -
    (∫ s in (0:ℝ)..t, F s)/(4*L)
  have hL : L ≠ 0 := (tc08_frequency_pos m).ne'
  apply (mul_right_inj' hL).mp
  field_simp
  linear_combination -4*hi

/-- The exact antiderivative needed to control the Volterra kernel. -/
theorem tc08_integral_sec_sq {t : ℝ} (ht : t ∈ Ico (0:ℝ) (Real.pi/2)) :
    (∫ s in (0:ℝ)..t, 1/(Real.cos s)^2) = Real.tan t := by
  have hdom {s : ℝ} (hs : s ∈ Icc (0:ℝ) t) :
      s ∈ Ioo (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [Real.pi_pos, hs.1], lt_of_le_of_lt hs.2 ht.2⟩
  have hc : ContinuousOn (fun s : ℝ => 1/(Real.cos s)^2) (Icc (0:ℝ) t) :=
    continuousOn_const.div (Real.continuous_cos.continuousOn.pow 2)
      (fun s hs => pow_ne_zero _ (tc08_cos_pos (hdom hs)).ne')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := t)
    (fun s hs => Real.hasDerivAt_tan (tc08_cos_pos
      (hdom (by simpa [uIcc_of_le ht.1] using hs))).ne')
    (hc.intervalIntegrable_of_Icc ht.1)
  simpa using h

/-- A quantitative error bound for the exact transformed equation. -/
theorem legendre_volterra_error (m : ℕ) {t : ℝ}
    (ht : t ∈ Ico (0:ℝ) (Real.pi/2)) :
    |tc08_u m t - tc08_initial m / tc08_frequency m *
      Real.sin (tc08_frequency m*t)| ≤
      (|tc08_initial m|/tc08_frequency m)*Real.tan t/(4*tc08_frequency m) := by
  let B := |tc08_initial m|/tc08_frequency m
  let F := fun s : ℝ => Real.sin (tc08_frequency m*(t-s))*tc08_u m s/(Real.cos s)^2
  have hdom {s : ℝ} (hs : s ∈ Icc (0:ℝ) t) :
      s ∈ Ioo (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [Real.pi_pos, hs.1], lt_of_le_of_lt hs.2 ht.2⟩
  have hF : ContinuousOn F (Icc (0:ℝ) t) := by
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · fun_prop
      · intro s hs
        exact (tc08_hasDerivAt_u m (hdom hs)).continuousAt.continuousWithinAt
    · fun_prop
    · intro s hs
      exact pow_ne_zero _ (tc08_cos_pos (hdom hs)).ne'
  have hG : ContinuousOn (fun s : ℝ => B/(Real.cos s)^2) (Icc (0:ℝ) t) :=
    continuousOn_const.div (Real.continuous_cos.continuousOn.pow 2)
      (fun s hs => pow_ne_zero _ (tc08_cos_pos (hdom hs)).ne')
  have hbound : (∫ s in (0:ℝ)..t, |F s|) ≤ B*Real.tan t := by
    calc
      _ ≤ ∫ s in (0:ℝ)..t, B/(Real.cos s)^2 := by
        apply intervalIntegral.integral_mono_on ht.1
          (hF.abs.intervalIntegrable_of_Icc ht.1) (hG.intervalIntegrable_of_Icc ht.1)
        intro s hs
        dsimp [F]
        rw [abs_div, abs_pow, sq_abs, abs_mul]
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        calc
          |Real.sin (tc08_frequency m*(t-s))| * |tc08_u m s| ≤ 1*B :=
            mul_le_mul (Real.abs_sin_le_one _) (legendre_transformed_amplitude m
              ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩) (abs_nonneg _) (by norm_num)
          _ = B := one_mul _
      _ = B*Real.tan t := by
        simp_rw [show ∀ s : ℝ, B/(Real.cos s)^2 = B*(1/(Real.cos s)^2) by
          intro s; ring]
        rw [intervalIntegral.integral_const_mul, tc08_integral_sec_sq ht]
  have h := legendre_volterra m ht
  have herr : tc08_u m t - tc08_initial m / tc08_frequency m *
      Real.sin (tc08_frequency m*t) = -(∫ s in (0:ℝ)..t, F s)/(4*tc08_frequency m) := by
    rw [h]
    dsimp [F]
    ring
  rw [herr, abs_div, abs_neg, abs_of_pos (mul_pos (by norm_num) (tc08_frequency_pos m))]
  exact div_le_div_of_nonneg_right
    ((intervalIntegral.abs_integral_le_integral_abs ht.1).trans hbound)
    (mul_nonneg (by norm_num) (tc08_frequency_pos m).le)

/-- The coefficient used in the odd Legendre residual expansion. -/
def tc08_coefficient (m : ℕ) : ℝ :=
  (-1 : ℝ)^m*(4*(m:ℝ)+3)*centralBinomial m/(4*(m:ℝ)+4)

/-- The exact sine amplitude after multiplying by the residual coefficient. -/
def tc08_scaledAmplitude (m : ℕ) : ℝ :=
  (2*(m:ℝ)+1)/(2*(m:ℝ)+2)*(centralBinomial m)^2

/-- Exact normalization of the signed initial derivative. -/
theorem tc08_coefficient_initial (m : ℕ) :
    tc08_coefficient m * (tc08_initial m / tc08_frequency m) = tc08_scaledAmplitude m := by
  have hs : (-1:ℝ)^m*(-1:ℝ)^m = 1 := by
    rw [← mul_pow]
    norm_num
  dsimp [tc08_coefficient, tc08_initial, tc08_frequency, tc08_scaledAmplitude]
  have h1 : (4*(m:ℝ)+4) ≠ 0 := by positivity
  have h2 : (2*(m:ℝ)+2) ≠ 0 := by positivity
  have h3 : (2*(m:ℝ)+3/2) ≠ 0 := by positivity
  calc
    _ = ((-1:ℝ)^m*(-1:ℝ)^m)*
        ((2*(m:ℝ)+1)/(2*(m:ℝ)+2)*(centralBinomial m)^2) := by
      field_simp
      ring
    _ = _ := by rw [hs, one_mul]

/-- The same normalization in absolute value. -/
theorem tc08_coefficient_initial_abs (m : ℕ) :
    |tc08_coefficient m| * (|tc08_initial m|/tc08_frequency m) = tc08_scaledAmplitude m := by
  have ha : 0 ≤ tc08_scaledAmplitude m := by
    dsimp [tc08_scaledAmplitude]
    positivity
  have h := congrArg abs (tc08_coefficient_initial m)
  rw [abs_mul, abs_div, abs_of_pos (tc08_frequency_pos m), abs_of_nonneg ha] at h
  exact h

/-- Wallis bounds give the exact bracket for the scaled sine amplitude. -/
theorem tc08_scaledAmplitude_bounds (m : ℕ) (hm : 1 ≤ m) :
    1/(Real.pi*((m:ℝ)+1)) ≤ tc08_scaledAmplitude m ∧
      tc08_scaledAmplitude m ≤ 1/(Real.pi*(m:ℝ)) := by
  have hw := central_binomial_wallis_bounds m hm
  have hmpos : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hratio : 0 ≤ (2*(m:ℝ)+1)/(2*(m:ℝ)+2) := by positivity
  have hratio' : (2*(m:ℝ)+1)/(2*(m:ℝ)+2) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2*(m:ℝ)+2)).2
    linarith
  constructor
  · calc
      1/(Real.pi*((m:ℝ)+1)) =
          (2*(m:ℝ)+1)/(2*(m:ℝ)+2) * (1/(Real.pi*((m:ℝ)+1/2))) := by
        field_simp <;> ring
      _ ≤ tc08_scaledAmplitude m := mul_le_mul_of_nonneg_left hw.1 hratio
  · calc
      tc08_scaledAmplitude m ≤ (centralBinomial m)^2 := by
        exact mul_le_of_le_one_left (sq_nonneg _) hratio'
      _ ≤ 1/(Real.pi*(m:ℝ)) := hw.2

/-- The scaled amplitude differs from `1/(πm)` by at most `1/(πm²)`. -/
theorem tc08_scaledAmplitude_error (m : ℕ) (hm : 1 ≤ m) :
    |tc08_scaledAmplitude m - 1/(Real.pi*(m:ℝ))| ≤ 1/(Real.pi*(m:ℝ)^2) := by
  have hb := tc08_scaledAmplitude_bounds m hm
  have hmpos : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [abs_of_nonpos (sub_nonpos.mpr hb.2)]
  calc
    -(tc08_scaledAmplitude m - 1/(Real.pi*(m:ℝ))) ≤
        1/(Real.pi*(m:ℝ))-1/(Real.pi*((m:ℝ)+1)) := by linarith [hb.1]
    _ = 1/(Real.pi*(m:ℝ)*((m:ℝ)+1)) := by field_simp; ring
    _ ≤ 1/(Real.pi*(m:ℝ)^2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [Real.pi_pos]

/-- A fully explicit sine estimate on the whole open positive half interval. -/
theorem tc08_scaled_sine_error (m : ℕ) (hm : 1 ≤ m) {t : ℝ}
    (ht : t ∈ Ico (0:ℝ) (Real.pi/2)) :
    |tc08_coefficient m * tc08_u m t -
      Real.sin (tc08_frequency m*t)/(Real.pi*(m:ℝ))| ≤
      (1+Real.tan t)/(Real.pi*(m:ℝ)^2) := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have htan : 0 ≤ Real.tan t :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two ht.1 ht.2.le
  have hL : 0 < tc08_frequency m := tc08_frequency_pos m
  have hLm : (m:ℝ) ≤ 4*tc08_frequency m := by
    dsimp [tc08_frequency]
    linarith
  have hraw := mul_le_mul_of_nonneg_left (legendre_volterra_error m ht)
    (abs_nonneg (tc08_coefficient m))
  have heq : tc08_coefficient m*tc08_u m t -
      tc08_scaledAmplitude m*Real.sin (tc08_frequency m*t) =
      tc08_coefficient m*(tc08_u m t - tc08_initial m/tc08_frequency m*
        Real.sin (tc08_frequency m*t)) := by
    rw [mul_sub, ← mul_assoc, tc08_coefficient_initial]
  have herr : |tc08_coefficient m*tc08_u m t -
      tc08_scaledAmplitude m*Real.sin (tc08_frequency m*t)| ≤
      tc08_scaledAmplitude m*Real.tan t/(4*tc08_frequency m) := by
    rw [heq, abs_mul]
    convert hraw using 1
    rw [show |tc08_coefficient m| *
        (|tc08_initial m|/tc08_frequency m*Real.tan t/(4*tc08_frequency m)) =
        (|tc08_coefficient m| * (|tc08_initial m|/tc08_frequency m))*Real.tan t /
          (4*tc08_frequency m) by ring, tc08_coefficient_initial_abs]
  have herr' : tc08_scaledAmplitude m*Real.tan t/(4*tc08_frequency m) ≤
      Real.tan t/(Real.pi*(m:ℝ)^2) := by
    calc
      _ ≤ (1/(Real.pi*(m:ℝ)))*Real.tan t/(4*tc08_frequency m) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (tc08_scaledAmplitude_bounds m hm).2 htan)
          (by positivity)
      _ ≤ (1/(Real.pi*(m:ℝ)))*Real.tan t/(m:ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hmpos hLm
      _ = _ := by ring
  have hamp : |tc08_scaledAmplitude m*Real.sin (tc08_frequency m*t) -
      Real.sin (tc08_frequency m*t)/(Real.pi*(m:ℝ))| ≤ 1/(Real.pi*(m:ℝ)^2) := by
    calc
      _ = |tc08_scaledAmplitude m-1/(Real.pi*(m:ℝ))| *
          |Real.sin (tc08_frequency m*t)| := by rw [← abs_mul]; congr 1; ring
      _ ≤ (1/(Real.pi*(m:ℝ)^2))*1 :=
        mul_le_mul (tc08_scaledAmplitude_error m hm) (Real.abs_sin_le_one _)
          (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  calc
    _ ≤ |tc08_coefficient m*tc08_u m t -
        tc08_scaledAmplitude m*Real.sin (tc08_frequency m*t)| +
        |tc08_scaledAmplitude m*Real.sin (tc08_frequency m*t) -
        Real.sin (tc08_frequency m*t)/(Real.pi*(m:ℝ))| := abs_sub_le _ _ _
    _ ≤ Real.tan t/(Real.pi*(m:ℝ)^2) + 1/(Real.pi*(m:ℝ)^2) :=
      add_le_add (herr.trans herr') hamp
    _ = _ := by ring


/-- An explicit uniform constant, before restricting to a moving endpoint. -/
theorem legendre_sine_error_explicit (m : ℕ) (hm : 1 ≤ m) {t : ℝ}
    (ht : t ∈ Ico (0:ℝ) (Real.pi/2)) :
    |tc08_coefficient m * (legendreRodrigues (2*m+1)).eval (Real.sin t) -
      Real.sin (tc08_frequency m*t)/(Real.pi*(m:ℝ)*Real.sqrt (Real.cos t))| ≤
      (1/Real.pi)*(1+Real.tan t)/((m:ℝ)^2*Real.sqrt (Real.cos t)) := by
  have hc := tc08_cos_pos (show t ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith [Real.pi_pos, ht.1], ht.2⟩)
  have hr : 0 < Real.sqrt (Real.cos t) := Real.sqrt_pos.2 hc
  have heq : tc08_coefficient m*(legendreRodrigues (2*m+1)).eval (Real.sin t) -
      Real.sin (tc08_frequency m*t)/(Real.pi*(m:ℝ)*Real.sqrt (Real.cos t)) =
      (tc08_coefficient m*tc08_u m t - Real.sin (tc08_frequency m*t)/(Real.pi*(m:ℝ))) /
        Real.sqrt (Real.cos t) := by
    dsimp [tc08_u]
    field_simp
  rw [heq, abs_div, abs_of_pos hr]
  calc
    _ ≤ ((1+Real.tan t)/(Real.pi*(m:ℝ)^2))/Real.sqrt (Real.cos t) :=
      div_le_div_of_nonneg_right (tc08_scaled_sine_error m hm ht) hr.le
    _ = _ := by ring


end AronowAudit.P023.Wave1
