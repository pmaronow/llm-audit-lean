import AronowAudit.P023.Wave1.Lib.PopulationProjectionTailC
import AronowAudit.P023.Wave1.Lib.ResidualLimitsTailC
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Finite Bernstein approximation and a uniform bound for Lipschitz population bias. -/
namespace AronowAudit.P023.Wave1
noncomputable section
open MeasureTheory Set Filter Polynomial
open scoped BigOperators Topology unitInterval

local instance tc11_lipschitz_uniform_probability : IsProbabilityMeasure uniformMargins :=
  ⟨uniform_law_normalized.1⟩

/-- A polynomial of degree at most `J` using the finite Bernstein weights. -/
def tc11_bernstein (h : ℝ → ℝ) (J : ℕ) : Polynomial ℝ :=
  (∑ k : Fin (J+1), Polynomial.C (h (2*(bernstein.z k : ℝ)-1)) *
    bernsteinPolynomial ℝ J k).comp (Polynomial.C (1/2) * Polynomial.X + Polynomial.C (1/2))

theorem tc11_bernstein_degree (h : ℝ → ℝ) (J : ℕ) :
    (tc11_bernstein h J).natDegree ≤ J := by
  have hb (k : Fin (J+1)) : (bernsteinPolynomial ℝ J k).natDegree ≤ J := by
    unfold bernsteinPolynomial
    have h1 : (1 - (Polynomial.X : Polynomial ℝ)).natDegree ≤ 1 := by compute_degree
    calc
      _ ≤ (Polynomial.X ^ (k : ℕ)).natDegree +
          ((1 - (Polynomial.X : Polynomial ℝ)) ^ (J-(k : ℕ))).natDegree :=
        (Polynomial.natDegree_mul_le).trans (Nat.add_le_add_right (by convert
          (Polynomial.natDegree_C_mul_le (J.choose k : ℝ) (Polynomial.X ^ (k : ℕ))) using 1 <;> simp) _)
      _ ≤ (k : ℕ) + (J-(k : ℕ)) := by
        gcongr
        · exact Polynomial.natDegree_X_pow_le _
        · exact (Polynomial.natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left (J-(k : ℕ)) h1)
      _ = J := by omega
  unfold tc11_bernstein
  calc
    _ ≤ (∑ k : Fin (J+1), Polynomial.C (h (2*(bernstein.z k : ℝ)-1)) *
        bernsteinPolynomial ℝ J k).natDegree *
        (Polynomial.C (1/2) * Polynomial.X + Polynomial.C (1/2) : Polynomial ℝ).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ J * 1 := Nat.mul_le_mul
      (by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro k _
        exact (Polynomial.natDegree_C_mul_le _ _).trans (hb k)) (by compute_degree)
    _ = J := by simp

theorem tc11_lipschitz_continuousOn (h : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |h x-h y| ≤ L*|x-y|) : ContinuousOn h (Icc (-1 : ℝ) 1) := by
  have hl : LipschitzOnWith (Real.toNNReal L) h (Icc (-1 : ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    simpa only [Real.dist_eq, Real.coe_toNNReal _ hL] using hlip
  exact hl.continuousOn

/-- The finite second-moment identity implies the needed square-root approximation rate. -/
theorem tc11_bernstein_error (h : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |h x-h y| ≤ L*|x-y|) (J : ℕ) (hJ : 1 ≤ J)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |h x - (tc11_bernstein h J).eval x| ≤ 2*L / Real.sqrt (J : ℝ) := by
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hs : 0 < Real.sqrt (J : ℝ) := Real.sqrt_pos.mpr hJp
  have hs2 : Real.sqrt (J : ℝ)^2 = J := Real.sq_sqrt hJp.le
  let u : I := ⟨(x+1)/2, by constructor <;> linarith [hx.1,hx.2]⟩
  have heval : (tc11_bernstein h J).eval x =
      ∑ k : Fin (J+1), bernstein J k u * h (2*(bernstein.z k : ℝ)-1) := by
    simp only [tc11_bernstein, Polynomial.eval_comp, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X]
    apply Finset.sum_congr rfl
    intro k _
    have he : (1/2 : ℝ)*x+1/2 = (u : ℝ) := by dsimp [u]; ring
    rw [he]
    change _ * bernstein J k u = _
    ring
  have hprob := bernstein.probability J u
  have hvar := bernstein.variance (by omega : J ≠ 0) u
  have hvarle : (u : ℝ)*(1-u)/(J : ℝ) ≤ 1/(J : ℝ) := by
    apply div_le_div_of_nonneg_right _ hJp.le
    have hu0 := u.2.1
    have hu1 := u.2.2
    nlinarith
  have hsum : (∑ k : Fin (J+1), bernstein J k u * |(u : ℝ)-(bernstein.z k : ℝ)|) ≤
      1 / Real.sqrt (J : ℝ) := by
    have hi (k : Fin (J+1)) : |(u : ℝ)-(bernstein.z k : ℝ)| ≤
        (((u : ℝ)-(bernstein.z k : ℝ))^2 * Real.sqrt (J : ℝ) +
          1/Real.sqrt (J : ℝ))/2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      have hh := sq_nonneg (|(u : ℝ)-(bernstein.z k : ℝ)| * Real.sqrt (J : ℝ)-1)
      have hsq := sq_abs ((u : ℝ)-(bernstein.z k : ℝ))
      have hsdiv : (1 / Real.sqrt (J : ℝ)) * Real.sqrt (J : ℝ) = 1 := by field_simp
      nlinarith
    calc
      _ ≤ ∑ k : Fin (J+1), bernstein J k u *
          ((((u : ℝ)-(bernstein.z k : ℝ))^2 * Real.sqrt (J : ℝ) +
          1/Real.sqrt (J : ℝ))/2) :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hi k) bernstein_nonneg)
      _ = (((u : ℝ)*(1-u)/(J : ℝ))*Real.sqrt (J : ℝ) +
          1/Real.sqrt (J : ℝ))/2 := by
        calc
          _ = ((∑ k : Fin (J+1), ((u : ℝ)-(bernstein.z k : ℝ))^2 * bernstein J k u) *
            Real.sqrt (J : ℝ) + (∑ k : Fin (J+1), bernstein J k u) / Real.sqrt (J : ℝ))/2 := by
              rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_add_distrib, Finset.sum_div]
              apply Finset.sum_congr rfl
              intro k _
              ring
          _ = _ := by rw [hvar,hprob]
      _ ≤ ((1/(J : ℝ))*Real.sqrt (J : ℝ) + 1/Real.sqrt (J : ℝ))/2 := by gcongr
      _ = _ := by field_simp; nlinarith
  rw [heval]
  have he : h x - (∑ k : Fin (J+1), bernstein J k u * h (2*(bernstein.z k : ℝ)-1)) =
      ∑ k : Fin (J+1), bernstein J k u * (h x-h (2*(bernstein.z k : ℝ)-1)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hprob, one_mul]
  rw [he]
  calc
    _ ≤ ∑ k : Fin (J+1), |bernstein J k u * (h x-h (2*(bernstein.z k : ℝ)-1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin (J+1), (2*L) * (bernstein J k u * |(u : ℝ)-(bernstein.z k : ℝ)|) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_of_nonneg bernstein_nonneg]
      have hz : 2*(bernstein.z k : ℝ)-1 ∈ Icc (-1 : ℝ) 1 := by
        constructor <;> nlinarith [(bernstein.z k).2.1, (bernstein.z k).2.2]
      have hl := hlip x hx _ hz
      have he : |x-(2*(bernstein.z k : ℝ)-1)| = 2*|(u : ℝ)-(bernstein.z k : ℝ)| := by
        rw [← abs_of_pos (by norm_num : (0 : ℝ)<2), ← abs_mul]
        congr 1
        dsimp [u]
        ring
      rw [he] at hl
      nlinarith [mul_le_mul_of_nonneg_left hl (bernstein_nonneg (n:=J) (ν:=k) (x:=u))]
    _ = (2*L) * ∑ k : Fin (J+1), bernstein J k u * |(u : ℝ)-(bernstein.z k : ℝ)| :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2*L) * (1/Real.sqrt (J : ℝ)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Multiplication by the piecewise polynomial residual preserves supported continuity integrability. -/
theorem tc11_residual_mul_continuousOn (J : ℕ) (h : ℝ → ℝ)
    (hc : ContinuousOn h (Icc (-1 : ℝ) 1)) :
    Integrable (fun x => popResidual uniformMargins J x * h x) uniformMargins := by
  have hi (p : Polynomial ℝ) : Integrable (fun x => p.eval x * h x) uniformMargins :=
    tc04_supported_continuous_integrable _ uniform_law_normalized.2 _
      (p.continuous.continuousOn.mul hc)
  have hf := Integrable.piecewise (s := Ici (0 : ℝ)) measurableSet_Ici
    (hi (1-projection uniformMargins J)).integrableOn
    (hi (-projection uniformMargins J)).integrableOn
  convert hf using 1
  funext x
  by_cases hx : 0 ≤ x <;> simp [popResidual, party, hx]

/-- Orthogonality and the actual residual L1 bound control the bias of any uniform approximation. -/
theorem tc11_bias_approximation_bound (h : ℝ → ℝ)
    (hc : ContinuousOn h (Icc (-1 : ℝ) 1)) (J : ℕ) (hJ : 1 ≤ J)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ J) (A : ℝ) (hA : 0 ≤ A)
    (he : ∀ x ∈ Icc (-1 : ℝ) 1, |h x-p.eval x| ≤ A) :
    |biasFunctional uniformMargins J h| ≤ A / Real.sqrt (residualVariance uniformMargins J) := by
  let v := residualVariance uniformMargins J
  have hv : 0 < v := (uniform_projection_variance J hJ).2.2.2
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hs2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
  have hzero := tc04_test J (projection uniformMargins J) p (tc04_chosen_spec J) hp
  have hmul := tc11_residual_mul_continuousOn J h hc
  have hpoly := tc04_residual_mul_integrable (projection uniformMargins J) p
  have hi := tc11_residual_mul_continuousOn J (fun x => h x-p.eval x)
    (hc.sub p.continuous.continuousOn)
  have hident : expectation uniformMargins (fun x => popResidual uniformMargins J x * h x) =
      expectation uniformMargins (fun x => popResidual uniformMargins J x * (h x-p.eval x)) := by
    simp_rw [mul_sub]
    unfold expectation at *
    rw [integral_sub hmul (show Integrable (fun x => popResidual uniformMargins J x*p.eval x) uniformMargins from hpoly)]
    change _ = _ - expectation uniformMargins (fun x => (party x-(projection uniformMargins J).eval x)*p.eval x)
    change expectation uniformMargins _ = 0 at hzero
    rw [hzero,sub_zero]
  have hbound : |expectation uniformMargins
      (fun x => popResidual uniformMargins J x * h x)| ≤ A*Real.sqrt v := by
    rw [hident]
    calc
      _ ≤ ∫ x, |popResidual uniformMargins J x * (h x-p.eval x)| ∂uniformMargins :=
        abs_integral_le_integral_abs
      _ ≤ ∫ x, A*|popResidual uniformMargins J x| ∂uniformMargins := by
        apply integral_mono_ae hi.abs ((tc09_residual_integrable J).abs.const_mul A)
        filter_upwards [show ∀ᵐ x ∂uniformMargins, x ∈ Icc (-1 : ℝ) 1 from
          ae_iff.mpr uniform_law_normalized.2] with x hx
        rw [abs_mul]
        nlinarith [mul_le_mul_of_nonneg_left (he x hx) (abs_nonneg (popResidual uniformMargins J x))]
      _ = A * expectation uniformMargins (fun x => |popResidual uniformMargins J x|) :=
        integral_const_mul _ _
      _ ≤ A * Real.sqrt v := mul_le_mul_of_nonneg_left (tc09_residual_l1_le_sqrt J hJ) hA
  unfold biasFunctional
  rw [abs_div, abs_of_pos hv]
  calc
    _ ≤ (A*Real.sqrt v)/v := div_le_div_of_nonneg_right hbound hv.le
    _ = A / Real.sqrt v := by field_simp; nlinarith

/-- A fixed Lipschitz function has uniformly bounded bias at every positive degree. -/
theorem lipschitz_bias_bounded (h : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |h x-h y| ≤ L*|x-y|) (J : ℕ) (hJ : 1 ≤ J) :
    |biasFunctional uniformMargins J h| ≤ 8*L := by
  let n := (J+1)/2
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hnJ : n ≤ J := by dsimp [n]; omega
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnc : (n : ℝ) ≤ J := by exact_mod_cast hnJ
  let v := residualVariance uniformMargins J
  have hv : 0 < v := (uniform_projection_variance J hJ).2.2.2
  have hvlo : 1/(16*(J : ℝ)) ≤ v := by
    calc
      _ ≤ 1/(16*(n : ℝ)) := one_div_le_one_div_of_le (by positivity) (by gcongr)
      _ ≤ centralBinomial n^2/4 := by
        calc
          _ = (1/(4*(n : ℝ)))/4 := by ring
          _ ≤ _ := div_le_div_of_nonneg_right (central_binomial_lower_bound n hn) (by norm_num)
      _ = v := ((uniform_projection_variance J hJ).2.2.1).symm
  have hs : 0 < Real.sqrt (J : ℝ) := Real.sqrt_pos.mpr hJp
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hprod : 1 ≤ 4*Real.sqrt (J : ℝ)*Real.sqrt v := by
    have hj2 := Real.sq_sqrt hJp.le
    have hv2 := Real.sq_sqrt hv.le
    have hvlo' := (div_le_iff₀ (by positivity : 0 < 16*(J : ℝ))).mp hvlo
    nlinarith [sq_nonneg (4*Real.sqrt (J : ℝ)*Real.sqrt v),
      mul_nonneg hs.le hsv.le]
  have hbound := tc11_bias_approximation_bound h (tc11_lipschitz_continuousOn h L hL hlip)
    J hJ (tc11_bernstein h J) (tc11_bernstein_degree h J)
    (2*L/Real.sqrt (J : ℝ)) (by positivity)
    (tc11_bernstein_error h L hL hlip J hJ)
  apply hbound.trans
  apply (div_le_iff₀ hsv).mpr
  apply (div_le_iff₀ hs).mpr
  nlinarith [mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 2*L)]

end
end AronowAudit.P023.Wave1
