import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
The Taylor coefficients at one are nonnegative.  The exact derivative
recurrences in `Polynomial.Chebyshev` give the bound for every nonnegative `s`; the upper bound on `s` in the node is unused.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n11_proof : N11 := by
  classical
  intro d hd s hs _hs_one
  let p : Polynomial ℝ := Chebyshev.T ℝ (d : ℤ)
  let q : Polynomial ℝ := taylor (1 : ℝ) p
  have hpdeg : p.natDegree = d := by
    simp [p, Chebyshev.natDegree_T]
  have hqdeg : q.natDegree = d := by
    simp [q, hpdeg]
  -- The factorial relation connects ordinary and Hasse derivatives, hence
  -- connects the library's derivative recurrence to the Taylor coefficients.
  have hfactor (k : ℕ) :
      (k.factorial : ℝ) * q.coeff k = (derivative^[k] p).eval 1 := by
    have hpoly : k.factorial • hasseDeriv k p = derivative^[k] p := by
      exact congrFun (factorial_smul_hasseDeriv (R := ℝ) k) p
    have heval := congrArg (fun r : Polynomial ℝ => r.eval 1) hpoly
    simpa [q, taylor_coeff, eval_smul, nsmul_eq_mul] using heval
  have hderiv : ∀ k : ℕ, k ≤ d → 0 ≤ (derivative^[k] p).eval 1 := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [p, Chebyshev.T_eval_one]
    | succ k ih =>
        intro hk
        have hkd : k ≤ d := by omega
        have hkR : (k : ℝ) ≤ (d : ℝ) := by exact_mod_cast hkd
        have hdiff : 0 ≤ (d : ℝ) ^ 2 - (k : ℝ) ^ 2 := by
          exact sub_nonneg.2 (pow_le_pow_left₀ (Nat.cast_nonneg k) hkR 2)
        have hrec := Chebyshev.iterate_derivative_T_eval_one_recurrence
          (R := ℝ) (d : ℤ) k
        push_cast at hrec
        change (2 * (k : ℝ) + 1) * (derivative^[k + 1] p).eval 1 =
          ((d : ℝ) ^ 2 - (k : ℝ) ^ 2) * (derivative^[k] p).eval 1 at hrec
        have hmul : 0 ≤ (2 * (k : ℝ) + 1) * (derivative^[k + 1] p).eval 1 := by
          rw [hrec]
          exact mul_nonneg hdiff (ih hkd)
        exact nonneg_of_mul_nonneg_right hmul (by positivity)
  have hcoeff (k : ℕ) : 0 ≤ q.coeff k := by
    by_cases hk : k ≤ d
    · have h := hderiv k hk
      rw [← hfactor k] at h
      exact nonneg_of_mul_nonneg_right h (by exact_mod_cast Nat.factorial_pos k)
    · simp only [coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < k), le_refl]
  have hthird :
      q.coeff 3 = (d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1) * ((d : ℝ) ^ 2 - 4) / 90 := by
    have h3 := Chebyshev.iterate_derivative_T_eval_one (R := ℝ) (d : ℤ) 3
    have hf := hfactor 3
    push_cast at h3
    norm_num [Finset.prod_range_succ] at h3
    norm_num at hf
    change 15 * (derivative^[3] p).eval 1 =
      (d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1) * ((d : ℝ) ^ 2 - 4) at h3
    rw [show (derivative^[3] p) = derivative (derivative (derivative p)) from rfl] at h3
    linarith
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdsq : (9 : ℝ) ≤ (d : ℝ) ^ 2 := by
    nlinarith
  have hhalf1 : (d : ℝ) ^ 2 / 2 ≤ (d : ℝ) ^ 2 - 1 := by nlinarith
  have hhalf4 : (d : ℝ) ^ 2 / 2 ≤ (d : ℝ) ^ 2 - 4 := by nlinarith
  have hfirst_nonneg : 0 ≤ (d : ℝ) ^ 2 - 1 := by linarith
  have hprod : (d : ℝ) ^ 6 / 4 ≤
      (d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1) * ((d : ℝ) ^ 2 - 4) := by
    calc
      (d : ℝ) ^ 6 / 4 =
          (d : ℝ) ^ 2 * ((d : ℝ) ^ 2 / 2) * ((d : ℝ) ^ 2 / 2) := by ring
      _ ≤ (d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1) * ((d : ℝ) ^ 2 - 4) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hhalf1 (sq_nonneg (d : ℝ))) hhalf4
          (by positivity) (mul_nonneg (sq_nonneg (d : ℝ)) hfirst_nonneg)
  have hthird_lower : (d : ℝ) ^ 6 / 720 ≤ q.coeff 3 := by
    rw [hthird]
    nlinarith [pow_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) 6]
  have heval : q.eval s = p.eval (1 + s) := by
    simpa [q, add_comm] using taylor_eval (1 : ℝ) p s
  have hterm : q.coeff 3 * s ^ 3 ≤ q.eval s := by
    rw [eval_eq_sum_range]
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (hcoeff k) (pow_nonneg hs k))
      (by simpa [hqdeg] using (show 3 < d + 1 by omega))
  change (d : ℝ) ^ 6 * s ^ 3 / 720 ≤ p.eval (1 + s)
  calc
    (d : ℝ) ^ 6 * s ^ 3 / 720 = ((d : ℝ) ^ 6 / 720) * s ^ 3 := by ring
    _ ≤ q.coeff 3 * s ^ 3 := mul_le_mul_of_nonneg_right hthird_lower (pow_nonneg hs 3)
    _ ≤ p.eval (1 + s) := by rwa [heval] at hterm

end

end AronowAudit.P001.Wave1.SieveRate
