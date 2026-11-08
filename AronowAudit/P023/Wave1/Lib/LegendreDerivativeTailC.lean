import AronowAudit.P023.Wave1.Lib.LegendreMomentsTailC
import AronowAudit.P023.Wave1.Lib.ProjectionCoreTailC

namespace AronowAudit.P023.Wave1
noncomputable section
open scoped BigOperators
open Polynomial MeasureTheory Set AronowAudit.Literature
local instance tc04_derivative_decidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Orthogonality extends to every strictly lower-degree polynomial. -/
theorem tc04_legendre_lower_orthogonality (n : ℕ) (p : Polynomial ℝ)
    (hp : p.degree < (n : WithBot ℕ)) :
    (∫ x in (-1:ℝ)..1, (legendreRodrigues n).eval x*p.eval x)=0 := by
  have hm : p ∈ Submodule.span ℝ (legendreRodrigues '' Iio n) := by
    rw [tc04_legendre_span_lt, Polynomial.mem_degreeLT]
    exact hp
  have hz : expectation uniformMargins (fun x => (legendreRodrigues n).eval x*p.eval x)=0 := by
    clear hp
    induction hm using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨k,hk,rfl⟩ := hq
      have hk' : k < n := hk
      rw [tc04_legendre_inner, if_neg (by omega)]
    | zero => simp [expectation]
    | add p q _ _ ihp ihq =>
      unfold expectation at *
      simp only [Polynomial.eval_add, mul_add]
      rw [integral_add (tc04_poly_mul_integrable _ _) (tc04_poly_mul_integrable _ _), ihp, ihq, add_zero]
    | smul a p _ ih =>
      unfold expectation at *
      simp only [Polynomial.eval_smul, smul_eq_mul]
      simp_rw [← mul_assoc, mul_comm ((legendreRodrigues n).eval _) a, mul_assoc]
      rw [integral_const_mul, ih, mul_zero]
  rw [tc04_uniform_expectation] at hz
  linarith

/-- Integration by parts with the exact two endpoint values. -/
theorem tc04_legendre_ibp (a b : ℕ) :
    (∫ x in (-1:ℝ)..1, (legendreRodrigues a).derivative.eval x*(legendreRodrigues b).eval x) =
      1-(-1:ℝ)^a*(-1:ℝ)^b-
        ∫ x in (-1:ℝ)..1, (legendreRodrigues a).eval x*(legendreRodrigues b).derivative.eval x := by
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => (legendreRodrigues b).eval x)
    (v := fun x : ℝ => (legendreRodrigues a).eval x)
    (u' := fun x : ℝ => (legendreRodrigues b).derivative.eval x)
    (v' := fun x : ℝ => (legendreRodrigues a).derivative.eval x)
    (a := (-1:ℝ)) (b := 1)
    (fun x _ => (legendreRodrigues b).hasDerivAt x)
    (fun x _ => (legendreRodrigues a).hasDerivAt x)
    ((legendreRodrigues b).derivative.continuous.intervalIntegrable (-1) 1)
    ((legendreRodrigues a).derivative.continuous.intervalIntegrable (-1) 1)
  have ha : (legendreRodrigues a).eval (-1)=(-1:ℝ)^a := by
    simpa only [tc04_legendre_one, mul_one] using tc04_legendre_parity a 1
  have hb : (legendreRodrigues b).eval (-1)=(-1:ℝ)^b := by
    simpa only [tc04_legendre_one, mul_one] using tc04_legendre_parity b 1
  simpa only [tc04_legendre_one, ha, hb, mul_one, mul_comm] using hi

/-- Adjacent derivatives have precisely the same moments as (2n+1)P_n. -/
theorem tc04_legendre_derivative_moments (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    expectation uniformMargins (fun x =>
      ((legendreRodrigues (n+1)).derivative.eval x-(legendreRodrigues (n-1)).derivative.eval x)*
        (legendreRodrigues k).eval x) = if k=n then 1 else 0 := by
  have hd (j : ℕ) : (legendreRodrigues j).derivative.degree < (j : WithBot ℕ) := by
    have h := Polynomial.degree_derivative_lt (tc04_legendre_sequence.ne_zero j)
    have he : (legendreRodrigues j).degree=(j : WithBot ℕ) := tc04_legendre_sequence.degree_eq j
    exact h.trans_eq he
  have hp := tc04_legendre_ibp (n+1) k
  have hp0 := tc04_legendre_lower_orthogonality (n+1) (legendreRodrigues k).derivative
    ((hd k).trans_le (by exact_mod_cast (show k ≤ n+1 by omega)))
  rw [hp0, sub_zero] at hp
  have hsub : (∫ x in (-1:ℝ)..1,
      ((legendreRodrigues (n+1)).derivative.eval x-(legendreRodrigues (n-1)).derivative.eval x)*
        (legendreRodrigues k).eval x) =
      (∫ x in (-1:ℝ)..1, (legendreRodrigues (n+1)).derivative.eval x*(legendreRodrigues k).eval x)-
      (∫ x in (-1:ℝ)..1, (legendreRodrigues (n-1)).derivative.eval x*(legendreRodrigues k).eval x) := by
    simp_rw [sub_mul]
    exact intervalIntegral.integral_sub
      (((legendreRodrigues (n+1)).derivative.continuous.mul (legendreRodrigues k).continuous).intervalIntegrable (-1) 1)
      (((legendreRodrigues (n-1)).derivative.continuous.mul (legendreRodrigues k).continuous).intervalIntegrable (-1) 1)
  rw [tc04_uniform_expectation, hsub, hp]
  by_cases he : k=n
  · subst k
    have hm0 := tc04_legendre_lower_orthogonality n (legendreRodrigues (n-1)).derivative
      ((hd (n-1)).trans_le (by exact_mod_cast (show n-1 ≤ n by omega)))
    have hm0' : (∫ x in (-1:ℝ)..1, (legendreRodrigues (n-1)).derivative.eval x*
        (legendreRodrigues n).eval x)=0 := by simpa only [mul_comm] using hm0
    rw [hm0', if_pos rfl]
    norm_num [pow_succ, ← mul_pow]
  · have hkn : k ≤ n-1 := by omega
    have hm := tc04_legendre_ibp (n-1) k
    have hm0 := tc04_legendre_lower_orthogonality (n-1) (legendreRodrigues k).derivative
      ((hd k).trans_le (by exact_mod_cast hkn))
    rw [hm0, sub_zero] at hm
    rw [hm, if_neg he]
    have hs : (-1:ℝ)^(n+1)=(-1:ℝ)^(n-1) := by
      rw [show n+1=(n-1)+2 by omega, pow_add]
      norm_num
    rw [hs]
    ring

end
end AronowAudit.P023.Wave1

namespace AronowAudit.Literature
open AronowAudit.P023 AronowAudit.P023.Wave1
open Polynomial MeasureTheory Set

/-- The full adjacent derivative identity, proved using orthogonality and endpoints. -/
theorem follandLegendreDerivativeIdentity_proof : FollandLegendreDerivativeIdentity := by
  intro n hn x
  let r : Polynomial ℝ := (legendreRodrigues (n+1)).derivative-
    (legendreRodrigues (n-1)).derivative-C (2*(n:ℝ)+1)*legendreRodrigues n
  have hr : r.natDegree ≤ n := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · exact (Polynomial.natDegree_derivative_le _).trans (by rw [tc04_legendre_degree]; omega)
      · exact (Polynomial.natDegree_derivative_le _).trans (by rw [tc04_legendre_degree]; omega)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by rw [tc04_legendre_degree])
  have ht : ∀ k ≤ n, expectation uniformMargins (fun y => r.eval y*(legendreRodrigues k).eval y)=0 := by
    intro k hk
    have he : (fun y => r.eval y*(legendreRodrigues k).eval y) =
        (fun y => ((legendreRodrigues (n+1)).derivative.eval y-(legendreRodrigues (n-1)).derivative.eval y)*
          (legendreRodrigues k).eval y -
          (2*(n:ℝ)+1)*((legendreRodrigues n).eval y*(legendreRodrigues k).eval y)) := by
      funext y
      simp [r]
      ring
    unfold expectation
    rw [he, integral_sub, integral_const_mul]
    · change expectation uniformMargins _ - (2*(n:ℝ)+1)*expectation uniformMargins _=0
      rw [tc04_legendre_derivative_moments n k hn hk, tc04_legendre_inner]
      by_cases heq : k=n
      · subst k
        simp [show 2*(n:ℝ)+1 ≠ 0 by positivity]
      · simp [heq,Ne.symm heq]
    · simpa only [Polynomial.eval_sub] using
        tc04_poly_mul_integrable ((legendreRodrigues (n+1)).derivative-(legendreRodrigues (n-1)).derivative)
          (legendreRodrigues k)
    · exact (tc04_poly_mul_integrable _ _).const_mul _
  have hz := tc04_legendre_test_span uniformMargins (fun y => r.eval y)
    (tc04_poly_mul_integrable r) n ht r hr
  have hr0 : r=0 := tc04_square_zero r (by simpa only [expectation, pow_two] using hz)
  have hx := congrArg (Polynomial.eval x) hr0
  simpa [r, sub_eq_zero] using hx

end AronowAudit.Literature
