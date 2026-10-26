/-
Upstream project: Causalean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
module
public import AronowAudit.External.Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.EndpointEnergy
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.Binomial
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Shifted Jacobi polynomials

The finite hypergeometric sum below is the Jacobi polynomial
`Pₖ^(α,β)(1 - 2x)` divided by `Pₖ^(α,β)(1)`.  In particular its
value at zero is one.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

open Polynomial

/-- A [real starting value](hyp:a) and [natural index](hyp:n) determine [the rising factorial](goal), [given by evaluating the corresponding rising-factorial polynomial](step:1).

The rising factorial `(a)ₙ`, evaluated as a real polynomial. -/
noncomputable def rising (a : ℝ) (n : ℕ) : ℝ :=
  (ascPochhammer ℝ n).eval a

/-- A [degree](hyp:k), [first shape parameter](hyp:α), [second shape parameter](hyp:β), and [evaluation point](hyp:x) determine [the normalized shifted Jacobi polynomial](goal), [given by its finite hypergeometric sum](step:1).

The normalized Jacobi polynomial `Pₖ^(α,β)(1 - 2x) / Pₖ^(α,β)(1)`.
This is the terminating hypergeometric expansion from DLMF 18.5.7. Each term divides by a rising
factorial of α + 1, so the formula is the Jacobi polynomial only when α + 1 is not a nonpositive
integer (in particular for the standard range α > −1); otherwise a vanishing denominator makes
the corresponding terms zero by the division-by-zero convention. -/
noncomputable def jacobiShifted (k : ℕ) (α β x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ m * (k.choose m : ℝ) *
      (rising ((k : ℝ) + α + β + 1) m / rising (α + 1) m) * x ^ m

/-- A [degree](hyp:k), [shape parameter](hyp:α), and [evaluation point](hyp:x) determine [the one-parameter shifted Jacobi perturbation](goal), [given by the normalized shifted Jacobi polynomial with second shape parameter zero](step:1).

The shifted Jacobi perturbation with the second parameter equal to zero. -/
noncomputable def h (k : ℕ) (α x : ℝ) : ℝ :=
  jacobiShifted k α 0 x

/-- A [positive real starting value](hyp:a) and [natural index](hyp:n), together with [its positivity](hyp:ha), ensure that [the associated rising factorial is positive](goal).

Every rising-factorial denominator used for a positive Jacobi parameter is positive. -/
theorem rising_pos (a : ℝ) (n : ℕ) (ha : 0 < a) : 0 < rising a n := by
  exact ascPochhammer_pos n a ha

/-- Any [degree](hyp:k) and [two shape parameters](hyp:α,β) give [a normalized shifted Jacobi polynomial equal to one at the left endpoint](goal).

The normalized shifted Jacobi polynomial has value one at the left endpoint. -/
theorem jacobiShifted_zero (k : ℕ) (α β : ℝ) : jacobiShifted k α β 0 = 1 := by
  unfold jacobiShifted
  calc
    _ = (-1 : ℝ) ^ 0 * (k.choose 0 : ℝ) *
        (rising ((k : ℝ) + α + β + 1) 0 / rising (α + 1) 0) * (0 : ℝ) ^ 0 := by
      apply Finset.sum_eq_single
      · intro b hb hne
        simp [hne]
      · simp
    _ = 1 := by simp [rising]

/-- A [degree](hyp:k), [coefficient index](hyp:m), and [two shape parameters](hyp:α,β), with [the first parameter above minus one](hyp:hα) and [the index below the degree](hyp:hm), give [the adjacent-coefficient recurrence for the normalized shifted Jacobi sum](goal).

Consecutive coefficients of the normalized shifted Jacobi sum satisfy
the hypergeometric recurrence.  This is the finite algebraic step behind
the Jacobi differential equation; it includes the top index `m = k-1`. -/
theorem jacobiShifted_coefficient_recurrence (k m : ℕ) (α β : ℝ)
    (hα : -1 < α) (hm : m < k) :
    ((m : ℝ) + 1) * (α + (m : ℝ) + 1) *
        ((-1 : ℝ) ^ (m + 1) * (k.choose (m + 1) : ℝ) *
          (rising ((k : ℝ) + α + β + 1) (m + 1) /
            rising (α + 1) (m + 1))) =
      -((k : ℝ) - (m : ℝ)) * ((k : ℝ) + α + β + (m : ℝ) + 1) *
        ((-1 : ℝ) ^ m * (k.choose m : ℝ) *
          (rising ((k : ℝ) + α + β + 1) m /
            rising (α + 1) m)) := by
  have hden : rising (α + 1) m ≠ 0 :=
    ne_of_gt (rising_pos (α + 1) m (by linarith))
  have hstep : α + (m : ℝ) + 1 ≠ 0 := by
    have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hchoose :
      (k.choose (m + 1) : ℝ) * ((m : ℝ) + 1) =
        (k.choose m : ℝ) * ((k : ℝ) - (m : ℝ)) := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq k m)
    push_cast at hc
    rw [Nat.cast_sub hm.le] at hc
    exact hc
  simp only [rising, ascPochhammer_succ_eval, pow_succ]
  change _ * _ * (_ * _ *
      (((ascPochhammer ℝ m).eval ((k : ℝ) + α + β + 1) *
          (((k : ℝ) + α + β + 1) + (m : ℝ))) /
        ((ascPochhammer ℝ m).eval (α + 1) * ((α + 1) + (m : ℝ))))) = _
  rw [show (α + 1) + (m : ℝ) = α + (m : ℝ) + 1 by ring]
  change (ascPochhammer ℝ m).eval (α + 1) ≠ 0 at hden
  field_simp [hden, hstep]
  linear_combination -((ascPochhammer ℝ m).eval ((k : ℝ) + α + β + 1)) *
    ((k : ℝ) + α + β + (m : ℝ) + 1) * hchoose

/-- A [degree](hyp:k), [two shape parameters](hyp:α,β), and [evaluation point](hyp:x), with [the first parameter above minus one](hyp:hα), give [the shifted Jacobi differential equation](goal).

The normalized shifted Jacobi polynomial satisfies its second-order
Jacobi differential equation when the normalization denominator is nonzero.
This coefficient identity is the first algebraic input to an endpoint
comparison proof; it follows term by term from the finite hypergeometric sum. -/
theorem jacobiShifted_ode (k : ℕ) (α β x : ℝ) (hα : -1 < α) :
    x * (1 - x) * deriv (deriv (jacobiShifted k α β)) x +
      (α + 1 - (α + β + 2) * x) * deriv (jacobiShifted k α β) x +
      (k : ℝ) * ((k : ℝ) + α + β + 1) * jacobiShifted k α β x = 0 := by
  let c : ℕ → ℝ := fun m =>
    (-1 : ℝ) ^ m * (k.choose m : ℝ) *
      (rising ((k : ℝ) + α + β + 1) m / rising (α + 1) m)
  let p : Polynomial ℝ := ∑ m ∈ Finset.range (k + 1), C (c m) * X ^ m
  have hp (m : ℕ) : p.coeff m = if m ≤ k then c m else 0 := by
    simp [p, Finset.mem_range]
  have hc (m : ℕ) (hm : m < k) :
      ((m : ℝ) + 1) * (α + (m : ℝ) + 1) * c (m + 1) =
        -((k : ℝ) - (m : ℝ)) * ((k : ℝ) + α + β + (m : ℝ) + 1) * c m := by
    exact jacobiShifted_coefficient_recurrence k m α β hα hm
  have hcoeff (m : ℕ) (K : ℝ) :
      (X * (1 - X) * derivative (derivative p) +
        (C (α + 1) - C (α + β + 2) * X) * derivative p + C K * p).coeff m =
        ((m : ℝ) + 1) * (α + (m : ℝ) + 1) * p.coeff (m + 1) +
        (K - (m : ℝ) * ((m : ℝ) + α + β + 1)) * p.coeff m := by
    have hform :
        X * (1 - X) * derivative (derivative p) +
        (C (α + 1) - C (α + β + 2) * X) * derivative p + C K * p =
        X * derivative (derivative p) - X * (X * derivative (derivative p)) +
        C (α + 1) * derivative p - X * (C (α + β + 2) * derivative p) +
        C K * p := by ring
    rw [hform]
    cases m with
    | zero =>
        simp only [coeff_add, coeff_sub, coeff_X_mul_zero, coeff_C_mul,
          coeff_derivative, Nat.cast_zero, zero_add, sub_zero]
        ring
    | succ m =>
        cases m with
        | zero =>
            simp only [coeff_add, coeff_sub, coeff_X_mul_zero, coeff_X_mul,
              coeff_C_mul, coeff_derivative, Nat.cast_succ, Nat.cast_zero]
            ring
        | succ m =>
            simp only [coeff_add, coeff_sub, coeff_X_mul, coeff_C_mul,
              coeff_derivative, Nat.cast_succ]
            ring
  have hpoly :
      X * (1 - X) * derivative (derivative p) +
        (C (α + 1) - C (α + β + 2) * X) * derivative p +
        C ((k : ℝ) * ((k : ℝ) + α + β + 1)) * p = 0 := by
    ext m
    rw [hcoeff, coeff_zero, hp, hp]
    by_cases hm : m < k
    · rw [if_pos hm.le, if_pos (Nat.succ_le_iff.mpr hm)]
      linear_combination hc m hm
    · by_cases heq : m = k
      · subst m
        simp only [if_pos le_rfl, if_neg (Nat.not_succ_le_self k), mul_zero, zero_add]
        ring
      · have hk : k < m := by omega
        simp only [if_neg (by omega : ¬ m + 1 ≤ k), if_neg (by omega : ¬ m ≤ k),
          mul_zero, add_zero]
  have heval (y : ℝ) : p.eval y = jacobiShifted k α β y := by
    simp [p, jacobiShifted, c, eval_finsetSum, eval_mul, eval_pow]
  have hfun : jacobiShifted k α β = fun y => p.eval y :=
    funext fun y => (heval y).symm
  rw [hfun]
  have hderivfun : deriv (fun y => p.eval y) = fun y => (derivative p).eval y :=
    funext fun y => Polynomial.deriv p
  rw [hderivfun]
  simp only [Polynomial.deriv]
  have := congrArg (Polynomial.eval x) hpoly
  simpa [eval_add, eval_mul, eval_sub] using this


end Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi
