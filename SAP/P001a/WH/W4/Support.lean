import SAP.P001a.Defs.WholeW4
import AronowAudit.P001.Wave1.Gap.TailBSieveEscape
import AronowAudit.P001.Wave1.SieveRate.N1
import AronowAudit.P001.Wave1.SieveRate.N2
import AronowAudit.P001.Wave1.SieveRate.N13

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Matrix

noncomputable section

namespace SAP.P001a.WH.W4

open AronowAudit.P001.Wave1.SieveRate
open AronowAudit.P001.Wave1.TailBSieveEscape

theorem coefficient_degree {d : ℕ} (b : Fin (d + 1) → ℝ) :
    (coefficientPolynomialW4 b).natDegree ≤ d := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  exact (Polynomial.natDegree_C_mul_X_pow_le (b k) (k : ℕ)).trans
    (Nat.le_of_lt_succ k.isLt)

theorem polynomial_of_coefficients {d : ℕ} (p : Polynomial ℝ)
    (hp : p.natDegree ≤ d) :
    p = coefficientPolynomialW4 (fun k : Fin (d + 1) => p.coeff (k : ℕ)) := by
  classical
  change p = ∑ k : Fin (d + 1), Polynomial.C (p.coeff (k : ℕ)) * Polynomial.X ^ (k : ℕ)
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => Polynomial.C (p.coeff k) * Polynomial.X ^ k) (d + 1)]
  exact p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hp)

/-- The ridge coefficient at positive regularization `1/(r+1)`. Its limit selects a
least-squares solution even when the design is singular or empty. -/
def ridgeCoefficient (n d r : ℕ) (z : SieveDataW4 n) : Fin (d + 1) → ℝ :=
  (((vand d z.1).transpose * vand d z.1) +
    (1 / ((r : ℝ) + 1)) • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ))⁻¹ |>.mulVec
    ((vand d z.1).transpose.mulVec z.2)

theorem measurable_ridge (n d r : ℕ) : Measurable (ridgeCoefficient n d r) := by
  classical
  let A : SieveDataW4 n → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    fun z => (vand d z.1).transpose * vand d z.1 +
      (1 / ((r : ℝ) + 1)) • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
  have hP : Continuous (fun z : SieveDataW4 n => vand d z.1) := by
    exact continuous_pi fun i => continuous_pi fun k =>
      (((continuous_apply i).comp continuous_fst).pow (k : ℕ))
  have hA : Continuous A := (hP.matrix_transpose.matrix_mul hP).add continuous_const
  have hAi (k l : Fin (d + 1)) : Measurable (fun z => (A z)⁻¹ k l) := by
    have hdet : Measurable (fun z => (A z).det⁻¹) := hA.matrix_det.measurable.inv
    have hadj : Measurable (fun z => (A z).adjugate k l) :=
      (hA.matrix_adjugate.matrix_elem k l).measurable
    simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
      Pi.mul_def] using hdet.mul hadj
  have hPy : Continuous (fun z : SieveDataW4 n => (vand d z.1).transpose.mulVec z.2) :=
    hP.matrix_transpose.matrix_mulVec continuous_snd
  apply Measurable.of_eval
  intro k
  change Measurable (fun z : SieveDataW4 n =>
    ∑ l : Fin (d + 1), (A z)⁻¹ k l * ((vand d z.1).transpose.mulVec z.2 l))
  exact Finset.measurable_sum Finset.univ fun l _ =>
    (hAi k l).mul (((continuous_apply l).comp hPy).measurable)

/-- Mathlib's shifted Legendre convention has value `(-1)^k` at the right endpoint. -/
def shiftedLegendreReal (k : ℕ) : Polynomial ℝ :=
  (Polynomial.shiftedLegendre k).map (Int.castRingHom ℝ)

theorem legendre_degree (k : ℕ) : (shiftedLegendreReal k).natDegree = k := by
  rw [shiftedLegendreReal, Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.natDegree_shiftedLegendre]

theorem legendre_at_one (k : ℕ) : (shiftedLegendreReal k).eval 1 = (-1 : ℝ) ^ k := by
  have h0 : (shiftedLegendreReal k).eval 0 = 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, shiftedLegendreReal, Polynomial.coeff_map,
      Polynomial.coeff_shiftedLegendre]
    simp
  have h := Polynomial.shiftedLegendre_eval_symm k (1 : ℝ)
  have he : (shiftedLegendreReal k).eval 1 =
      (-1 : ℝ) ^ k * (shiftedLegendreReal k).eval 0 := by
    simpa only [shiftedLegendreReal, Polynomial.eval_map, Polynomial.aeval_def, sub_self,
      algebraMap_int_eq]
      using h
  rw [he, h0, mul_one]

/-- One integration by parts computes the norm from lower-degree orthogonality and the
right endpoint. This avoids a separate beta-integral proof of the Legendre norm. -/
theorem orthogonal_endpoint_norm (p : Polynomial ℝ) (k : ℕ) (hp : p.natDegree = k)
    (ho : ∀ q : Polynomial ℝ, q.degree < (k : WithBot ℕ) →
      (∫ x in Set.Icc (0 : ℝ) 1, q.eval x * p.eval x) = 0) :
    (∫ x in Set.Icc (0 : ℝ) 1, (p.eval x) ^ 2) = (p.eval 1) ^ 2 / (2 * (k : ℝ) + 1) := by
  let I : Polynomial ℝ → ℝ := fun r => ∫ x in Set.Icc (0 : ℝ) 1, r.eval x
  have hsub (r s : Polynomial ℝ) : I (r - s) = I r - I s := by
    simp only [I, Polynomial.eval_sub]
    exact integral_sub r.continuous.integrableOn_Icc s.continuous.integrableOn_Icc
  have hadd (r s : Polynomial ℝ) : I (r + s) = I r + I s := by
    simp only [I, Polynomial.eval_add]
    exact integral_add r.continuous.integrableOn_Icc s.continuous.integrableOn_Icc
  have hconst (a : ℝ) (r : Polynomial ℝ) : I (Polynomial.C a * r) = a * I r := by
    simp only [I, Polynomial.eval_mul, Polynomial.eval_C, integral_const_mul]
  have hFTC (r : Polynomial ℝ) : I r.derivative = r.eval 1 - r.eval 0 := by
    change (∫ x in Set.Icc (0 : ℝ) 1, r.derivative.eval x) = _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => r.hasDerivAt x) (r.derivative.continuous.intervalIntegrable 0 1)
  have hdeg : (Polynomial.X * p.derivative - Polynomial.C (k : ℝ) * p).degree <
      (k : WithBot ℕ) := by
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro n hn
    cases n with
    | zero =>
      have hk : k = 0 := by omega
      simp [hk]
    | succ n =>
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
        Polynomial.coeff_C_mul]
      by_cases hnk : n + 1 = k
      · rw [← hnk]
        push_cast
        ring
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < n + 1 by omega)]
        ring
  have hx : I (p * (Polynomial.X * p.derivative - Polynomial.C (k : ℝ) * p)) = 0 := by
    simpa only [I, Polynomial.eval_mul, mul_comm] using ho _ hdeg
  have he : p * (Polynomial.X * p.derivative - Polynomial.C (k : ℝ) * p) =
      p * (Polynomial.X * p.derivative) - Polynomial.C (k : ℝ) * (p * p) := by ring
  rw [he, hsub, hconst] at hx
  have hd := hFTC (Polynomial.X * (p * p))
  have hderiv : (Polynomial.X * (p * p)).derivative =
      p * p + Polynomial.C 2 * (p * (Polynomial.X * p.derivative)) := by
    simp only [Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.C_ofNat]
    ring
  rw [hderiv, hadd, hconst] at hd
  simp only [Polynomial.eval_mul, Polynomial.eval_X, one_mul, zero_mul, sub_zero] at hd
  have hden : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  have hI : I (p * p) = (p.eval 1) ^ 2 / (2 * (k : ℝ) + 1) := by
    apply (eq_div_iff hden).2
    nlinarith [hd, hx]
  simpa only [I, Polynomial.eval_mul, pow_two] using hI

/-- The endpoint reproducing kernel, normalized to have value one at `1`. -/
def endpointKernel (d : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / ((d : ℝ) + 1) ^ 2) *
    ∑ k : Fin (d + 1),
      Polynomial.C (((2 * (k : ℕ) + 1 : ℕ) : ℝ) * (-1 : ℝ) ^ (k : ℕ)) *
        shiftedLegendreReal (k : ℕ)

/-- Designs on which the kernel's empirical squared norm is at most two. -/
def goodDesign (n : ℕ) (q : Polynomial ℝ) : Set (Fin n → ℝ) :=
  {x | Function.Injective x ∧ ∑ i : Fin n, (q.eval (x i)) ^ 2 ≤ 2}

theorem measurable_goodDesign (n : ℕ) (q : Polynomial ℝ) :
    MeasurableSet (goodDesign n q) := by
  classical
  have hinj : MeasurableSet {x : Fin n → ℝ | Function.Injective x} := by
    have heq : {x : Fin n → ℝ | Function.Injective x} =
        ⋂ i : Fin n, ⋂ j : Fin n, {x : Fin n → ℝ | x i = x j → i = j} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Function.Injective]
    rw [heq]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : i = j
    · simp [hij]
    · convert (measurableSet_eq_fun (f := fun x : Fin n → ℝ => x i)
        (g := fun x => x j) (measurable_pi_apply i) (measurable_pi_apply j)).compl using 1
      ext x
      simp [hij]
  have hsum : Measurable (fun x : Fin n → ℝ => ∑ i : Fin n, (q.eval (x i)) ^ 2) :=
    Finset.measurable_sum Finset.univ fun i _ =>
      (q.continuous.measurable.comp (measurable_pi_apply i)).pow_const 2
  exact hinj.inter (measurableSet_le hsum measurable_const)

end SAP.P001a.WH.W4
