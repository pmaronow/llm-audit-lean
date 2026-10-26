/-
Upstream project: Causalean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Repeated integration by parts and removal of a left endpoint

These statements are parameter-free calculus tools.  They are formulated for
ordinary derivatives on a finite interval and for the interval integral over
`[0,1]`, so subsequent special-function proofs need only supply the boundary
values and local smoothness.
-/

public section

namespace Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

open Filter MeasureTheory intervalIntegral
open scoped Topology

private theorem contDiffAt_iterate_deriv_on (a b : ℝ) (g : ℝ → ℝ)
    (hg : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ ⊤ g x) (n : ℕ) :
    ∀ x ∈ Set.Icc a b, ContDiffAt ℝ ⊤ (deriv^[n] g) x := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
      intro x hx
      simpa only [Function.iterate_succ_apply'] using
        (ih x hx).derivWithin (m := ⊤) (by simp)

/-- A [smooth factor](hyp:g), [power order](hyp:k), and [derivative order](hyp:i), when [the factor is smooth at one](hyp:hg) and [the derivative order is below the power order](hyp:hi), give [a zero derivative at the right endpoint for the power bump](goal).

Multiplication by `(1-x)^k` forces every ordinary derivative of order
less than `k` to vanish at `x=1`, provided the other factor is smooth there. -/
theorem iter_deriv_mul_one_sub_pow_at_one (g : ℝ → ℝ) (k i : ℕ)
    (hg : ContDiffAt ℝ ⊤ g 1) (hi : i < k) :
    (deriv^[i] (fun x : ℝ => g x * (1 - x) ^ k)) 1 = 0 := by
  rw [← iteratedDeriv_eq_iterate]
  have hp : ContDiffAt ℝ i (fun x : ℝ => (1 - x) ^ k) 1 := by fun_prop
  change iteratedDeriv i (g * (fun x : ℝ => (1 - x) ^ k)) 1 = 0
  rw [iteratedDeriv_mul (hg.of_le (by simp)) hp]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjle : j ≤ i := by omega
  have hlt : i - j < k := by omega
  have hpow : iteratedDeriv (i - j) (fun x : ℝ => (1 - x) ^ k) 1 = 0 := by
    rw [iteratedDeriv_comp_const_sub (i - j) (fun y : ℝ => y ^ k) 1]
    simp only [sub_self, iteratedDeriv_pow]
    have hpos : 0 < k - (i - j) := by omega
    rw [zero_pow (Nat.ne_of_gt hpos), mul_zero, smul_zero]
  rw [hpow]
  ring

/-- An [integration order](hyp:k), [interval endpoints](hyp:a,b), and [two smooth functions](hyp:p,f), when [the first function is smooth on the interval](hyp:hp), [the second function is smooth on the interval](hyp:hf), and [the interval has positive length](hyp:hab), give [the repeated integration-by-parts identity with all endpoint products](goal).

Repeated integration by parts transfers `k` derivatives from `f` to `p`
and records all endpoint products explicitly.  This form applies on a
truncated interval whose left endpoint terms vanish only in a limit. -/
theorem integral_mul_iterated_deriv_with_boundary (k : ℕ) (a b : ℝ)
    (p f : ℝ → ℝ)
    (hp : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ ⊤ p x)
    (hf : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ ⊤ f x)
    (hab : a < b) :
    (∫ x in a..b, p x * (deriv^[k] f) x) =
      (∑ i ∈ Finset.range k,
        (-1 : ℝ) ^ i *
          ((deriv^[i] p) b * (deriv^[k - 1 - i] f) b -
           (deriv^[i] p) a * (deriv^[k - 1 - i] f) a)) +
        (-1 : ℝ) ^ k *
          (∫ x in a..b, (deriv^[k] p) x * f x) := by
  induction k generalizing p f with
  | zero => simp
  | succ k ih =>
      have hfd : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ ⊤ (deriv f) x := by
        simpa only [Function.iterate_one] using contDiffAt_iterate_deriv_on a b f hf 1
      have hpk := contDiffAt_iterate_deriv_on a b p hp k
      have hpk' := contDiffAt_iterate_deriv_on a b p hp (k + 1)
      have hintp : IntervalIntegrable (deriv^[k + 1] p) volume a b := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hab.le]
        intro x hx
        exact (hpk' x hx).continuousAt.continuousWithinAt
      have hintf : IntervalIntegrable (deriv f) volume a b := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hab.le]
        intro x hx
        exact (hfd x hx).continuousAt.continuousWithinAt
      have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (u := deriv^[k] p) (v := f)
        (u' := deriv^[k + 1] p) (v' := deriv f)
        (by
          intro x hx
          have hx' : x ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab.le] using hx
          simpa only [Function.iterate_succ_apply'] using
            ((hpk x hx').differentiableAt (by simp)).hasDerivAt)
        (by
          intro x hx
          have hx' : x ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab.le] using hx
          exact ((hf x hx').differentiableAt (by simp)).hasDerivAt)
        hintp hintf
      have hih := ih p (deriv f) hp hfd
      simp_rw [← Function.iterate_succ_apply] at hih
      have hsum :
          (∑ i ∈ Finset.range k,
            (-1 : ℝ) ^ i *
              ((deriv^[i] p) b * (deriv^[(k - 1 - i).succ] f) b -
               (deriv^[i] p) a * (deriv^[(k - 1 - i).succ] f) a)) =
          (∑ i ∈ Finset.range k,
            (-1 : ℝ) ^ i *
              ((deriv^[i] p) b * (deriv^[k - i] f) b -
               (deriv^[i] p) a * (deriv^[k - i] f) a)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hlt : i < k := Finset.mem_range.mp hi
        have heq : (k - 1 - i).succ = k - i := by omega
        rw [heq]
      rw [hih, hip, hsum, Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel_right, Nat.sub_self, Function.iterate_zero, id_eq]
      rw [pow_succ]
      ring

/-- An [integration order](hyp:k), [interval endpoints](hyp:a,b), and [two smooth functions](hyp:p,f), when [the first function is smooth on the interval](hyp:hp), [the second function is smooth on the interval](hyp:hf), [all lower derivatives of the second function vanish at both endpoints](hyp:hbd), and [the interval has positive length](hyp:hab), give [the boundary-free repeated integration-by-parts identity: the integral over the interval of the first function times the k-th derivative of the second equals (−1)^k times the integral of the k-th derivative of the first times the second](goal).

If every derivative of `f` below order `k` vanishes at both endpoints,
then `k` integrations by parts transfer all derivatives from `f` to `p`.
The smoothness assumptions hold on the closed integration interval. -/
theorem integral_mul_iterated_deriv_eq (k : ℕ) (a b : ℝ) (p f : ℝ → ℝ)
    (hp : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ ⊤ p x)
    (hf : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ ⊤ f x)
    (hbd : ∀ i < k, (deriv^[i] f) a = 0 ∧ (deriv^[i] f) b = 0)
    (hab : a < b) :
    (∫ x in a..b, p x * (deriv^[k] f) x) =
      (-1 : ℝ) ^ k * (∫ x in a..b, (deriv^[k] p) x * f x) := by
  have hsum :
      (∑ i ∈ Finset.range k,
        (-1 : ℝ) ^ i *
          ((deriv^[i] p) b * (deriv^[k - 1 - i] f) b -
           (deriv^[i] p) a * (deriv^[k - 1 - i] f) a)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have hlt : k - 1 - i < k := by omega
    obtain ⟨ha, hb⟩ := hbd (k - 1 - i) hlt
    simp [ha, hb]
  simpa only [hsum, zero_add] using
    (integral_mul_iterated_deriv_with_boundary k a b p f hp hf hab)


end Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi
