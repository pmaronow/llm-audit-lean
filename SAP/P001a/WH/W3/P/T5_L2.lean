import SAP.P001a.WH.W3.Leaves
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Polynomial

namespace SAP.P001a.WH.W3.P.T5_L2

private theorem kernel_derivative_vanishes (k i : ℕ) (hi : i < k) (z : ℝ)
    (hz : z = 0 ∨ z = 1) :
    ((Polynomial.derivative^[i])
      ((Polynomial.X : Polynomial ℝ)^k * (1 - Polynomial.X)^k)).eval z = 0 := by
  have hk : k ≠ 0 := by omega
  have hroot : (((Polynomial.X : Polynomial ℝ) * (1 - Polynomial.X)).eval z) = 0 := by
    rcases hz with rfl | rfl <;> simp
  have hd : (Polynomial.X - Polynomial.C z : Polynomial ℝ) ∣
      (Polynomial.X * (1 - Polynomial.X) : Polynomial ℝ) :=
    Polynomial.dvd_iff_isRoot.mpr hroot
  have hqd : (Polynomial.X - Polynomial.C z : Polynomial ℝ)^k ∣
      (Polynomial.X^k * (1 - Polynomial.X)^k : Polynomial ℝ) := by
    simpa only [mul_pow] using (pow_dvd_pow_of_dvd hd k)
  have hd' := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd i hqd
  have hlin : (Polynomial.X - Polynomial.C z : Polynomial ℝ) ∣
      (Polynomial.X - Polynomial.C z)^(k-i) := by
    simpa only [pow_one] using
      (pow_dvd_pow (Polynomial.X - Polynomial.C z : Polynomial ℝ) (show 1 ≤ k-i by omega))
  apply Polynomial.dvd_iff_isRoot.mp
  exact hlin.trans hd'

private theorem repeated_integration_by_parts (k : ℕ) (p q : Polynomial ℝ)
    (hq0 : ∀ i, i < k → ((Polynomial.derivative^[i]) q).eval 0 = 0)
    (hq1 : ∀ i, i < k → ((Polynomial.derivative^[i]) q).eval 1 = 0) :
    (∫ x in (0 : ℝ)..1, p.eval x * ((Polynomial.derivative^[k]) q).eval x) =
      (-1 : ℝ)^k *
        (∫ x in (0 : ℝ)..1, ((Polynomial.derivative^[k]) p).eval x * q.eval x) := by
  induction k generalizing p q with
  | zero => simp
  | succ k ih =>
    let qk : Polynomial ℝ := (Polynomial.derivative^[k]) q
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (p.continuous.continuousOn) (qk.continuous.continuousOn)
      (fun x _ => p.hasDerivAt x) (fun x _ => qk.hasDerivAt x)
      ((p.derivative.continuous).intervalIntegrable 0 1)
      ((qk.derivative.continuous).intervalIntegrable 0 1)
    have hqk0 : qk.eval 0 = 0 := by simpa [qk] using hq0 k (by omega)
    have hqk1 : qk.eval 1 = 0 := by simpa [qk] using hq1 k (by omega)
    have hparts' :
        (∫ x in (0 : ℝ)..1, p.eval x * ((Polynomial.derivative^[k.succ]) q).eval x) =
          - (∫ x in (0 : ℝ)..1, p.derivative.eval x *
            ((Polynomial.derivative^[k]) q).eval x) := by
      simpa [qk, Function.iterate_succ_apply', hqk0, hqk1] using hparts
    have hih := ih p.derivative q (fun i hi => hq0 i (by omega))
      (fun i hi => hq1 i (by omega))
    have hiter :
        (Polynomial.derivative^[k]) p.derivative =
          (Polynomial.derivative^[k.succ]) p := by
      simp only [Function.iterate_succ_apply]
    rw [hparts', hih, hiter]
    ring

end SAP.P001a.WH.W3.P.T5_L2

theorem SAP.P001a.WH.W3.T5_L2_proof : SAP.P001a.WH.W3.T5_L2 := by
  intro k p hp
  let q : Polynomial ℝ := (Polynomial.X : Polynomial ℝ)^k * (1 - Polynomial.X)^k
  have hRod : Polynomial.C (k.factorial : ℝ) * SAP.P001a.WH.W3.shiftedLegendreReal k =
      (Polynomial.derivative^[k]) q := by
    have h := congrArg (Polynomial.map (Int.castRingHom ℝ))
      (Polynomial.factorial_mul_shiftedLegendre_eq k)
    simpa [q, SAP.P001a.WH.W3.shiftedLegendreReal,
      ← Polynomial.iterate_derivative_map] using h
  have hq0 : ∀ i, i < k → ((Polynomial.derivative^[i]) q).eval 0 = 0 := by
    intro i hi
    exact SAP.P001a.WH.W3.P.T5_L2.kernel_derivative_vanishes k i hi 0 (Or.inl rfl)
  have hq1 : ∀ i, i < k → ((Polynomial.derivative^[i]) q).eval 1 = 0 := by
    intro i hi
    exact SAP.P001a.WH.W3.P.T5_L2.kernel_derivative_vanishes k i hi 1 (Or.inr rfl)
  have hrep := SAP.P001a.WH.W3.P.T5_L2.repeated_integration_by_parts k p q hq0 hq1
  have hderiv : (Polynomial.derivative^[k]) p = 0 :=
    Polynomial.iterate_derivative_eq_zero_of_degree_lt hp
  rw [hderiv] at hrep
  simp only [Polynomial.eval_zero, zero_mul, intervalIntegral.integral_zero,
    mul_zero] at hrep
  have hpoint (x : ℝ) :
      p.eval x * ((Polynomial.derivative^[k]) q).eval x =
        (k.factorial : ℝ) * (p.eval x * (SAP.P001a.WH.W3.shiftedLegendreReal k).eval x) := by
    calc
      _ = p.eval x *
          (Polynomial.C (k.factorial : ℝ) * SAP.P001a.WH.W3.shiftedLegendreReal k).eval x := by
            rw [← hRod]
      _ = _ := by simp [Polynomial.eval_mul]; ring
  have hscale :
      (∫ x in (0 : ℝ)..1, p.eval x * ((Polynomial.derivative^[k]) q).eval x) =
        (k.factorial : ℝ) *
          (∫ x in (0 : ℝ)..1,
            p.eval x * (SAP.P001a.WH.W3.shiftedLegendreReal k).eval x) := by
    rw [intervalIntegral.integral_congr (fun x _ => hpoint x), intervalIntegral.integral_const_mul]
  have hfactor : (k.factorial : ℝ) ≠ 0 := by positivity
  have hint :
      (∫ x in (0 : ℝ)..1,
        p.eval x * (SAP.P001a.WH.W3.shiftedLegendreReal k).eval x) = 0 := by
    apply (mul_left_cancel₀ hfactor)
    calc
      (k.factorial : ℝ) *
          (∫ x in (0 : ℝ)..1,
            p.eval x * (SAP.P001a.WH.W3.shiftedLegendreReal k).eval x) =
        (∫ x in (0 : ℝ)..1, p.eval x * ((Polynomial.derivative^[k]) q).eval x) := hscale.symm
      _ = (k.factorial : ℝ) * 0 := by rw [hrep]; ring
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact hint
