import AronowAudit.P001.Wave1.PolynomialBlpBlueprint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Support

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.PolynomialBlp

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Realize finite-dimensional least squares in `Lp ℝ 2 μ`, including singular designs. -/
theorem n4_proof : N4.{u} := by
  classical
  intro h3 Ω _ μ _ X Y hX hY hq J
  let P : (Fin (J + 1) → ℝ) → Polynomial ℝ := fun c =>
    ∑ k : Fin (J + 1), Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)
  have hdegree (c : Fin (J + 1) → ℝ) : (P c).natDegree ≤ J := by
    refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
      (fun k : Fin (J + 1) => Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)) ?_
    intro k hk
    exact (Polynomial.natDegree_C_mul_X_pow_le (c k) (k : ℕ)).trans (by omega)
  have heval (c : Fin (J + 1) → ℝ) (x : ℝ) :
      (P c).eval x = ∑ k : Fin (J + 1), c k * x ^ (k : ℕ) := by
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  let v : Fin (J + 1) → Lp ℝ 2 μ := fun k =>
    (hq (Polynomial.X ^ (k : ℕ))).toLp (fun ω =>
      (Polynomial.X ^ (k : ℕ) : Polynomial ℝ).eval (X ω))
  let y : Lp ℝ 2 μ := hY.toLp Y
  have hv : ∀ᵐ ω ∂μ, ∀ k : Fin (J + 1), (v k) ω = X ω ^ (k : ℕ) := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [(hq (Polynomial.X ^ (k : ℕ))).coeFn_toLp] with ω hω
    simpa only [v, Polynomial.eval_pow, Polynomial.eval_X] using hω
  -- Both sides represent the same finite linear combination almost everywhere.
  have hclass (c : Fin (J + 1) → ℝ) :
      (hq (P c)).toLp (fun ω => (P c).eval (X ω)) = ∑ k, c k • v k := by
    apply Lp.ext
    have hsmul : ∀ᵐ ω ∂μ, ∀ k : Fin (J + 1),
        (c k • v k) ω = c k * (v k) ω := by
      apply ae_all_iff.mpr
      intro k
      filter_upwards [Lp.coeFn_smul (c k) (v k)] with ω hω
      simpa only [Pi.smul_apply, smul_eq_mul] using hω
    filter_upwards [(hq (P c)).coeFn_toLp,
      Lp.coeFn_fun_finsetSum Finset.univ (fun k => c k • v k), hsmul, hv]
      with ω hpω hsumω hsmulω hvω
    rw [hpω, hsumω, heval]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsmulω k, hvω k]
  -- The L² inner product gives the squared norm as the integral of the square.
  have hnorm (f : Ω → ℝ) (hf : MemLp f 2 μ) :
      ‖hf.toLp f‖ ^ 2 = mean μ (fun ω => f ω ^ 2) := by
    calc
      ‖hf.toLp f‖ ^ 2 = inner ℝ (hf.toLp f) (hf.toLp f) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = ∫ ω, ((hf.toLp f) ω) ^ 2 ∂μ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        exact ae_of_all _ (fun ω => by
          simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs])
      _ = mean μ (fun ω => f ω ^ 2) := by
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp] with ω hω
        rw [hω]
  have hrisk (q : Polynomial ℝ) :
      mean μ (fun ω => (Y ω - q.eval (X ω)) ^ 2) =
        ‖y - (hq q).toLp (fun ω => q.eval (X ω))‖ ^ 2 := by
    dsimp only [y]
    rw [← MemLp.toLp_sub hY (hq q)]
    exact (hnorm (fun ω => Y ω - q.eval (X ω)) (hY.sub (hq q))).symm
  obtain ⟨b, hb⟩ := h3 (J + 1) v y
  refine ⟨P b, hdegree b, ?_⟩
  intro q hqdeg
  let c : Fin (J + 1) → ℝ := fun k => q.coeff (k : ℕ)
  have hqP : P c = q := by
    dsimp only [P, c]
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => Polynomial.C (q.coeff k) * Polynomial.X ^ k) (J + 1)]
    exact (q.as_sum_range_C_mul_X_pow' (by omega)).symm
  have hright : (∑ k, c k • v k) = (hq q).toLp (fun ω => q.eval (X ω)) := by
    calc
      (∑ k, c k • v k) = (hq (P c)).toLp (fun ω => (P c).eval (X ω)) :=
        (hclass c).symm
      _ = (hq q).toLp (fun ω => q.eval (X ω)) := by rw [hqP]
  have hnormle := hb c
  rw [← hclass b, hright] at hnormle
  have hsq : ‖y - (hq (P b)).toLp (fun ω => (P b).eval (X ω))‖ ^ 2 ≤
      ‖y - (hq q).toLp (fun ω => q.eval (X ω))‖ ^ 2 := by
    have hprod := mul_nonneg
      (sub_nonneg.mpr hnormle)
      (add_nonneg
        (norm_nonneg (y - (hq q).toLp (fun ω => q.eval (X ω))))
        (norm_nonneg (y - (hq (P b)).toLp (fun ω => (P b).eval (X ω)))))
    nlinarith
  rw [hrisk (P b), hrisk q]
  exact hsq

end

end AronowAudit.P001.Wave1.PolynomialBlp
