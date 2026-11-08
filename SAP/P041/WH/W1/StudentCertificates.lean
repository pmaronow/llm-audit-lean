import SAP.P041.WH.W1.Helpers

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W1
open MeasureTheory
open scoped BigOperators

theorem student197_density_eq_reference (t : ℝ) :
    Student197DensityW1 t = AronowAudit.P040.studentReferenceDensity 197 t := by
  unfold Student197DensityW1 AronowAudit.P040.studentReferenceDensity
  norm_num

theorem student197_tail_eq_reference (x : ℝ) :
    Student197TailW1 x = AronowAudit.P040.studentReferenceP (x^2) 197 := by
  unfold Student197TailW1 AronowAudit.P040.studentReferenceP
  simp only [Real.sqrt_sq_eq_abs, student197_density_eq_reference]

/-- The finite Student polynomials integrate exactly, at every real endpoint.
Continuity supplies every required interval-integrability fact. -/
theorem student197_polynomial_integral (n : ℕ) (x : ℝ) :
    (∫ t in (0 : ℝ)..x, Student197TaylorW1 n (t^2/197)) = Student197IntegratedW1 n x := by
  have he (t : ℝ) (j : ℕ) :
      (-1 : ℝ)^j * (Nat.choose (98+j) j : ℝ) * (t^2/197)^j =
        ((-1 : ℝ)^j * (Nat.choose (98+j) j : ℝ) / (197 : ℝ)^j) * t^(2*j) := by
    rw [div_pow, ← pow_mul]
    ring
  simp only [Student197TaylorW1, he]
  rw [intervalIntegral.integral_finsetSum (fun j _ => (by fun_prop :
    Continuous (fun t : ℝ => ((-1 : ℝ)^j * (Nat.choose (98+j) j : ℝ) /
      (197 : ℝ)^j) * t^(2*j))).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    zero_pow (by omega : 2*_+1 ≠ 0), sub_zero]
  unfold Student197IntegratedW1
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end SAP.P041.WH.W1
