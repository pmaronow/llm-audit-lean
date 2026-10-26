import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Support

/-!
Pointwise least-squares selection for all samples, including empty and singular designs.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n4_proof : N4 := by
  classical
  intro hBlp Ω X Y J
  have hex (n : ℕ) (ω : Ω) :
      ∃ p : Polynomial ℝ, p.natDegree ≤ J n ∧
        ∀ q : Polynomial ℝ, q.natDegree ≤ J n →
          (∑ i ∈ Finset.range n, (Y i ω - p.eval (X i ω)) ^ 2) ≤
            ∑ i ∈ Finset.range n, (Y i ω - q.eval (X i ω)) ^ 2 := by
    let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => Y i ω)
    let v : Fin (J n + 1) → EuclideanSpace ℝ (Fin n) :=
      fun k => WithLp.toLp 2 (fun i => X i ω ^ (k : ℕ))
    obtain ⟨b, hb⟩ := hBlp (J n + 1) v y
    have hdegree (c : Fin (J n + 1) → ℝ) : (coeffPoly c).natDegree ≤ J n := by
      unfold coeffPoly
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro k _
      exact (Polynomial.natDegree_C_mul_X_pow_le (c k) (k : ℕ)).trans
        (Nat.le_of_lt_succ k.isLt)
    have hsum (c : Fin (J n + 1) → ℝ) (i : Fin n) :
        (∑ k, c k • v k) i = (coeffPoly c).eval (X i ω) := by
      change (WithLp.ofLp (∑ k, c k • v k)) i = _
      simp [WithLp.ofLp_sum, v, coeffPoly, Polynomial.eval_finsetSum]
    have hnorm (c : Fin (J n + 1) → ℝ) :
        ‖y - ∑ k, c k • v k‖ ^ 2 =
          ∑ i ∈ Finset.range n, (Y i ω - (coeffPoly c).eval (X i ω)) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [PiLp.sub_apply, y, PiLp.toLp_apply, hsum]
      exact Fin.sum_univ_eq_sum_range
        (fun i => (Y i ω - (coeffPoly c).eval (X i ω)) ^ 2) n
    refine ⟨coeffPoly b, hdegree b, ?_⟩
    intro q hq
    have hqrep : q = coeffPoly (d := J n) (fun k => q.coeff (k : ℕ)) := by
      simpa only [coeffPoly, Finset.sum_range, Nat.succ_eq_add_one] using
        (q.as_sum_range_C_mul_X_pow' (lt_of_le_of_lt hq (Nat.lt_succ_self _)))
    have hsquares :
        ‖y - ∑ k, b k • v k‖ ^ 2 ≤
          ‖y - ∑ k : Fin (J n + 1), q.coeff (k : ℕ) • v k‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hb (fun k => q.coeff (k : ℕ)))
    rw [hnorm b, hnorm (fun k => q.coeff (k : ℕ)), ← hqrep] at hsquares
    exact hsquares
  refine ⟨fun n ω => (hex n ω).choose, ?_⟩
  intro n ω
  exact (hex n ω).choose_spec

end

end AronowAudit.P001.Wave1.SieveRate
