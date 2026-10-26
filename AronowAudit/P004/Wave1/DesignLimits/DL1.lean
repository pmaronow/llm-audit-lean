import AronowAudit.P004.Wave1.DesignLimitsBlueprint

namespace AronowAudit.P004.Wave1.DesignLimits

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Positivity of finite-design event probabilities, used by the limit nodes. -/
theorem prob_nonneg_finite {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A : Assignment N → Prop) : 0 ≤ prob p A := by
  classical
  have h := expect_mono p hp (fun _ => 0) (fun z => if A z then 1 else 0) (by
    intro z
    split_ifs <;> norm_num)
  rw [expect_const] at h
  exact h

/-- An event contained in a union has probability at most the sum of the two probabilities. -/
theorem prob_le_add_of_imp_finite {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A B C : Assignment N → Prop)
    (h : ∀ z, A z → B z ∨ C z) : prob p A ≤ prob p B + prob p C := by
  classical
  have hpoint : ∀ z, (if A z then 1 else 0 : ℝ) ≤
      (if B z then 1 else 0) + (if C z then 1 else 0) := by
    intro z
    have hz := h z
    by_cases ha : A z <;> by_cases hb : B z <;> by_cases hc : C z <;>
      norm_num [ha, hb, hc] at *
  calc
    prob p A ≤ expect p (fun z =>
        (if B z then 1 else 0) + (if C z then 1 else 0)) := expect_mono p hp _ _ hpoint
    _ = prob p B + prob p C := expect_add p _ _

/-- Markov and Chebyshev, proved by pointwise bounds on the bad-event indicator. -/
theorem dl1_proof : DL1 := by
  classical
  intro N p hp U ε hε
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  constructor
  · have hpoint : ∀ z, (if ε < |U z| then 1 else 0 : ℝ) ≤ |U z| / ε := by
      intro z
      by_cases hz : ε < |U z|
      · rw [if_pos hz]
        exact (le_div_iff₀ hε).2 (by linarith)
      · rw [if_neg hz]
        exact div_nonneg (abs_nonneg (U z)) hε.le
    calc
      prob p (fun z => ε < |U z|) ≤ expect p (fun z => |U z| / ε) :=
        expect_mono p hp _ _ hpoint
      _ = expect p (fun z => |U z|) / ε := expect_div p _ ε
  · have hpoint : ∀ z, (if ε < |U z| then 1 else 0 : ℝ) ≤ (U z) ^ 2 / ε ^ 2 := by
      intro z
      by_cases hz : ε < |U z|
      · rw [if_pos hz]
        apply (le_div_iff₀ hεsq).2
        have hprod : 0 ≤ (|U z| - ε) * (|U z| + ε) :=
          mul_nonneg (by linarith) (by positivity)
        nlinarith [sq_abs (U z)]
      · rw [if_neg hz]
        exact div_nonneg (sq_nonneg (U z)) hεsq.le
    calc
      prob p (fun z => ε < |U z|) ≤ expect p (fun z => (U z) ^ 2 / ε ^ 2) :=
        expect_mono p hp _ _ hpoint
      _ = expect p (fun z => (U z) ^ 2) / ε ^ 2 := expect_div p _ (ε ^ 2)

end
end AronowAudit.P004.Wave1.DesignLimits
