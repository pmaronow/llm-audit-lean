import AronowAudit.Literature.CondP023
import AronowAudit.External.Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.Legendre
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.ComputeDegree

noncomputable section
open MeasureTheory Set Polynomial
open scoped BigOperators

namespace AronowAudit.P023.Wave1

local instance tc04_legendre_decidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Iterated differentiation under an affine polynomial substitution. -/
theorem tc04_iterate_comp_affine (p : Polynomial ℝ) (a b : ℝ) (k : ℕ) :
    (derivative^[k]) (p.comp (C a * X + C b)) =
      C (a ^ k) * ((derivative^[k]) p).comp (C a * X + C b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_comp,
      derivative_add, derivative_X, mul_one, add_zero]
    rw [Function.iterate_succ_apply', pow_succ, C_mul]
    ring

/-- The shifted Mathlib convention and the Rodrigues convention agree. -/
theorem tc04_legendre_shift (n : ℕ) (x : ℝ) :
    (AronowAudit.Literature.legendreRodrigues n).eval x =
      Polynomial.aeval ((1-x)/2) (Polynomial.shiftedLegendre n) := by
  let A : Polynomial ℝ := C (-1/2) * X + C (1/2)
  let b : Polynomial ℝ := X^n * (1-X)^n
  let s := (Polynomial.shiftedLegendre n).map (algebraMap ℤ ℝ)
  have hf : C (n.factorial : ℝ) * s = (derivative^[n]) b := by
    have h := congrArg (Polynomial.map (algebraMap ℤ ℝ))
      (Polynomial.factorial_mul_shiftedLegendre_eq n)
    simpa [s, b, ← Polynomial.iterate_derivative_map] using h
  have hb : b.comp A = C ((-1/4 : ℝ)^n) * (X^2-1)^n := by
    simp only [b, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.sub_comp, Polynomial.one_comp]
    rw [Polynomial.C_pow, ← mul_pow, ← mul_pow]
    congr 1
    apply Polynomial.funext
    intro y
    simp [A]
    ring
  have hd := congrArg (fun p : Polynomial ℝ => ((derivative^[n]) p).eval x) hb
  rw [tc04_iterate_comp_affine, Polynomial.iterate_derivative_C_mul] at hd
  have he : (-1/2 : ℝ)^n * ((n.factorial : ℝ) * s.eval ((1-x)/2)) =
      (-1/4 : ℝ)^n * ((derivative^[n]) ((X^2-1 : Polynomial ℝ)^n)).eval x := by
    simpa only [A, hf.symm, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_X, show (-1/2:ℝ)*x+1/2=(1-x)/2 by ring] using hd
  have hsc : (-1/4 : ℝ)^n * (2:ℝ)^n = (-1/2 : ℝ)^n := by
    rw [← mul_pow]; norm_num
  have hc : (-1/2 : ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have he' : (2:ℝ)^n * (n.factorial : ℝ) * s.eval ((1-x)/2) =
      ((derivative^[n]) ((X^2-1 : Polynomial ℝ)^n)).eval x := by
    apply mul_left_cancel₀ hc
    calc
      _ = ((-1/2:ℝ)^n * ((n.factorial:ℝ)*s.eval ((1-x)/2))) * 2^n := by ring
      _ = ((-1/4:ℝ)^n * ((derivative^[n]) ((X^2-1:Polynomial ℝ)^n)).eval x)*2^n := by rw [he]
      _ = ((-1/4:ℝ)^n*2^n) * ((derivative^[n]) ((X^2-1:Polynomial ℝ)^n)).eval x := by ring
      _ = _ := by rw [hsc]
  have hs : s.eval ((1-x)/2) =
      Polynomial.aeval ((1-x)/2) (Polynomial.shiftedLegendre n) := by
    simp [s, Polynomial.eval_map, Polynomial.aeval_def]
  rw [← hs]
  dsimp [AronowAudit.Literature.legendreRodrigues]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [← he']
  field_simp

/-- Exact degree, including degree zero. -/
theorem tc04_legendre_degree (n : ℕ) :
    (AronowAudit.Literature.legendreRodrigues n).natDegree = n := by
  have hp : AronowAudit.Literature.legendreRodrigues n =
      ((Polynomial.shiftedLegendre n).map (algebraMap ℤ ℝ)).comp
        (C (-1/2) * X + C (1/2)) := by
    apply Polynomial.funext
    intro x
    simpa only [Polynomial.eval_comp, Polynomial.eval_map, Polynomial.aeval_def,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      show (-1/2:ℝ)*x+1/2=(1-x)/2 by ring] using tc04_legendre_shift n x
  rw [hp, Polynomial.natDegree_comp, Polynomial.natDegree_map_eq_of_injective
    Int.cast_injective, Polynomial.natDegree_shiftedLegendre]
  norm_num [Polynomial.natDegree_add_C]

/-- Reflection parity inherited from the shifted integer polynomials. -/
theorem tc04_legendre_parity (n : ℕ) (x : ℝ) :
    (AronowAudit.Literature.legendreRodrigues n).eval (-x) =
      (-1 : ℝ)^n * (AronowAudit.Literature.legendreRodrigues n).eval x := by
  rw [tc04_legendre_shift, tc04_legendre_shift, Polynomial.shiftedLegendre_eval_symm]
  congr 1
  congr 1
  ring

/-- Normalization at the right endpoint. -/
theorem tc04_legendre_one (n : ℕ) :
    (AronowAudit.Literature.legendreRodrigues n).eval 1 = 1 := by
  rw [tc04_legendre_shift]
  norm_num only [sub_self, zero_div]
  rw [← Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.jacobiShifted_zero_zero_eq_shiftedLegendre]
  exact Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.jacobiShifted_zero n 0 0

end AronowAudit.P023.Wave1

namespace AronowAudit.Literature
open AronowAudit.P023.Wave1

/-- The full Folland orthogonality proposition, with its prescribed normalization. -/
theorem follandLegendreOrthogonality_proof : FollandLegendreOrthogonality := by
  intro m n
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  simp_rw [tc04_legendre_shift]
  have h := intervalIntegral.integral_comp_sub_mul
    (fun t : ℝ => Polynomial.aeval t (Polynomial.shiftedLegendre m) *
      Polynomial.aeval t (Polynomial.shiftedLegendre n))
    (a := (-1:ℝ)) (b := 1) (c := (1/2:ℝ)) (by norm_num) (1/2)
  have he (x : ℝ) : (1-x)/2 = 1/2-(1/2)*x := by ring
  simp_rw [he]
  rw [h]
  norm_num only [one_div, inv_inv, mul_one, mul_neg_one, neg_neg,
    show (1/2:ℝ)-1/2=0 by norm_num, show (1/2:ℝ)+1/2=1 by norm_num,
    smul_eq_mul]
  rw [Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.shiftedLegendre_orthogonal_unit]
  by_cases hm : m=n
  · subst n; simp; ring
  · simp [hm]

end AronowAudit.Literature

namespace AronowAudit.P023.Wave1
open AronowAudit.Literature

/-- The lower derivatives of the Rodrigues kernel vanish at either endpoint. -/
theorem tc04_rodrigues_boundary (n i : ℕ) (hi : i < n) (z : ℝ)
    (hz : z=1 ∨ z = -1) :
    ((derivative^[i]) ((X^2-1 : Polynomial ℝ)^n)).eval z = 0 := by
  have hd : (X-C z : Polynomial ℝ) ∣ X^2-1 := by
    apply Polynomial.dvd_iff_isRoot.mpr
    rcases hz with rfl | rfl <;> norm_num [Polynomial.IsRoot]
  have hd' := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd i
    (pow_dvd_pow_of_dvd hd n)
  apply Polynomial.dvd_iff_isRoot.mp
  have hlin : (X-C z : Polynomial ℝ) ∣ (X-C z)^(n-i) := by
    simpa only [pow_one] using (pow_dvd_pow (X-C z : Polynomial ℝ) (show 1 ≤ n-i by omega))
  exact hlin.trans hd'

/-- The even coefficients of the symmetric Rodrigues kernel. -/
theorem tc04_rodrigues_even_coeff (n m : ℕ) :
    ((X^2-1 : Polynomial ℝ)^n).coeff (2*m) =
      (-1 : ℝ)^(n-m) * (n.choose m : ℝ) := by
  have he : (X^2-1 : Polynomial ℝ)^n =
      Polynomial.expand ℝ 2 ((X+C (-1 : ℝ))^n) := by
    simp only [map_pow, map_add, Polynomial.expand_X, Polynomial.expand_C]
    congr 1
    simp [sub_eq_add_neg]
  rw [he, Polynomial.coeff_expand_mul' (by norm_num), Polynomial.coeff_X_add_C_pow]

/-- The exact odd half-interval moment, obtained by integrating Rodrigues once. -/
theorem odd_legendre_half_moment (m : ℕ) :
    (∫ x in (0 : ℝ)..1, (legendreRodrigues (2*m+1)).eval x) =
      (-1 : ℝ)^m * centralBinomial m / (2*(m : ℝ)+2) := by
  let q : Polynomial ℝ := (derivative^[2*m]) ((X^2-1 : Polynomial ℝ)^(2*m+1))
  have hi : (∫ x in (0:ℝ)..1, q.derivative.eval x) = q.eval 1-q.eval 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => q.hasDerivAt x)
      (q.derivative.continuous.intervalIntegrable 0 1)
  have hq1 : q.eval 1 = 0 := tc04_rodrigues_boundary _ _ (by omega) _ (Or.inl rfl)
  have hq0 : q.eval 0 =
      ((2*m).factorial : ℝ) * ((-1 : ℝ)^(m+1) * ((2*m+1).choose m : ℝ)) := by
    dsimp [q]
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
    simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
    rw [tc04_rodrigues_even_coeff, show 2*m+1-m=m+1 by omega]
  have he : (∫ x in (0:ℝ)..1, (legendreRodrigues (2*m+1)).eval x) =
      ((2^(2*m+1) * ((2*m+1).factorial : ℝ))⁻¹) * (q.eval 1-q.eval 0) := by
    unfold legendreRodrigues
    rw [Function.iterate_succ_apply']
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [intervalIntegral.integral_const_mul, hi]
  rw [he, hq1, hq0]
  have hc := congrArg (fun k : ℕ => (k:ℝ)) (Nat.choose_mul_succ_eq (2*m) m)
  have hm : 2*m+1-m=m+1 := by omega
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, hm] at hc
  rw [Nat.factorial_succ]
  rw [show (2:ℝ)^(2*m+1)=4^m*2 by rw [pow_succ, pow_mul]; norm_num,
    pow_succ (-1:ℝ) m]
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, zero_sub,
    centralBinomial] at *
  field_simp
  nlinarith [hc]

end AronowAudit.P023.Wave1

namespace AronowAudit.P023.Wave1
open AronowAudit.Literature

@[simp] theorem tc04_legendre_zero : legendreRodrigues 0 = 1 := by
  simp [legendreRodrigues]

/-- The Rodrigues polynomials form a polynomial sequence. -/
def tc04_legendre_sequence : Polynomial.Sequence ℝ where
  elems' := legendreRodrigues
  degree_eq' n := by
    rw [Polynomial.degree_eq_natDegree (show legendreRodrigues n ≠ 0 from by
      intro hz
      have h := tc04_legendre_one n
      rw [hz, Polynomial.eval_zero] at h
      norm_num at h), tc04_legendre_degree]

/-- All polynomials of degree at most J lie in the first J+1 Legendre span. -/
theorem tc04_legendre_span (J : ℕ) :
    Submodule.span ℝ (legendreRodrigues '' Iic J) = Polynomial.degreeLE ℝ J := by
  exact tc04_legendre_sequence.span_degreeLE (fun i _ =>
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr
      (tc04_legendre_sequence.ne_zero i)))


/-- Orthogonality for the normalized uniform probability law. -/
theorem tc04_legendre_inner (m n : ℕ) :
    expectation uniformMargins (fun x => (legendreRodrigues m).eval x *
      (legendreRodrigues n).eval x) = if m=n then 1/(2*(n:ℝ)+1) else 0 := by
  unfold expectation uniformMargins
  rw [integral_smul_measure, follandLegendreOrthogonality_proof m n]
  by_cases hm : m=n <;> simp [hm] <;> ring

/-- Multiplying by the party indicator restricts the uniform integral to [0,1]. -/
theorem tc04_uniform_party_poly (p : Polynomial ℝ) :
    expectation uniformMargins (fun x => party x*p.eval x) =
      (1/2:ℝ) * ∫ x in (0:ℝ)..1, p.eval x := by
  have he : (fun x : ℝ => party x*p.eval x) = (Ici (0:ℝ)).indicator (fun x => p.eval x) := by
    funext x
    by_cases hx : 0 ≤ x <;> simp [party, hx, Set.indicator]
  have hi : Ici (0:ℝ) ∩ Icc (-1:ℝ) 1 = Icc (0:ℝ) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨h0, _, h1⟩; exact ⟨h0,h1⟩
    · rintro ⟨h0,h1⟩; exact ⟨h0,by linarith,h1⟩
  unfold expectation uniformMargins
  rw [integral_smul_measure, he, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, hi, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  norm_num

/-- Positive even Legendre degrees have zero half-interval integral. -/
theorem tc04_legendre_half_even (m : ℕ) :
    (∫ x in (0:ℝ)..1, (legendreRodrigues (2*m+2)).eval x) = 0 := by
  let p := legendreRodrigues (2*m+2)
  have hp : ∀ x : ℝ, p.eval (-x)=p.eval x := by
    intro x
    dsimp [p]
    rw [tc04_legendre_parity]
    simp [pow_add, pow_mul]
  have hz := follandLegendreOrthogonality_proof 0 (2*m+2)
  simp only [tc04_legendre_zero, Polynomial.eval_one, one_mul,
    if_neg (show ¬ 0=2*m+2 by omega)] at hz
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1:ℝ) ≤ 1 by norm_num)] at hz
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (p.continuous.intervalIntegrable (μ := volume) (-1:ℝ) 0)
    (p.continuous.intervalIntegrable (μ := volume) (0:ℝ) 1)
  have hn : (∫ x in (-1:ℝ)..0, p.eval x) = ∫ x in (0:ℝ)..1, p.eval x := by
    have h := intervalIntegral.integral_comp_neg (fun x => p.eval x) (a := (0:ℝ)) (b := 1)
    simp only [neg_zero] at h
    simpa only [hp] using h.symm
  change (∫ x in (-1:ℝ)..1, p.eval x)=0 at hz
  rw [hn] at hadd
  linarith

/-- Testing a linear integral identity on a Legendre basis suffices. -/
theorem tc04_legendre_test_span (μ : Measure ℝ) (f : ℝ → ℝ)
    (hint : ∀ p : Polynomial ℝ, Integrable (fun x => f x*p.eval x) μ)
    (J : ℕ) (hzero : ∀ k ≤ J, (∫ x, f x*(legendreRodrigues k).eval x ∂μ)=0)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ J) : (∫ x, f x*p.eval x ∂μ)=0 := by
  have hmem : p ∈ Submodule.span ℝ (legendreRodrigues '' Iic J) := by
    rw [tc04_legendre_span, Polynomial.mem_degreeLE]
    exact Polynomial.degree_le_of_natDegree_le hp
  clear hp
  induction hmem using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨k,hk,rfl⟩ := hq
    exact hzero k hk
  | zero => simp
  | add p q _ _ ihp ihq =>
    simp only [Polynomial.eval_add, mul_add]
    rw [integral_add (hint p) (hint q), ihp, ihq, add_zero]
  | smul a p _ ih =>
    simp only [Polynomial.eval_smul, smul_eq_mul]
    simp_rw [← mul_assoc, mul_comm (f _) a, mul_assoc]
    rw [integral_const_mul, ih, mul_zero]

end AronowAudit.P023.Wave1
