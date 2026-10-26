/-
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import AronowAudit.External.Causalean.Stat.FiniteDesign.DesignCore

/-!
# Finite Chebyshev inequality

This file proves `FiniteDesign.chebyshev`, the finite-design Chebyshev inequality
`Pr[ε ≤ |X - E X|] ≤ Var X / ε ^ 2` for a statistic on a finite assignment space.
The proof works directly from `FiniteDesign.Pr`, `FiniteDesign.E`, and `FiniteDesign.Var`, so it
can be used in design-based consistency arguments without moving through the measure-theoretic
probability layer.
-/

public section

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased
namespace FiniteDesign

variable {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)

open Classical in
/-- **Finite-design Chebyshev inequality.** In a finite design, for any statistic `X` and
[a strictly positive threshold `ε`](hyp:hε), [the design probability that `X` differs from its
design mean by at least `ε` is at most the design variance of `X` divided by `ε²`](goal). -/
theorem chebyshev (X : Ω → ℝ) {ε : ℝ} (hε : 0 < ε) :
    D.Pr (fun z => ε ≤ |X z - D.E X|) ≤ D.Var X / ε ^ 2 := by
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  -- Monotonicity of a finite sum (proved from scratch: the ordered-`BigOperators`
  -- module is not in scope here, only the basic algebraic one).
  have hmono : ∀ (s : Finset Ω) (a b : Ω → ℝ), (∀ i ∈ s, a i ≤ b i) →
      ∑ i ∈ s, a i ≤ ∑ i ∈ s, b i := by
    intro s
    induction s using Finset.induction with
    | empty => intro a b _; simp
    | insert x t hx ih =>
        intro a b h
        rw [Finset.sum_insert hx, Finset.sum_insert hx]
        exact add_le_add (h x (Finset.mem_insert_self x t))
          (ih a b (fun i hi => h i (Finset.mem_insert_of_mem hi)))
  -- Core inequality: `ε² * Pr(event) ≤ Var X`.
  have hcore : ε ^ 2 * D.Pr (fun z => ε ≤ |X z - D.E X|) ≤ D.Var X := by
    -- Write both sides as `∑ z, D.p z * (…)`, then compare term by term.
    have hlhs : ε ^ 2 * D.Pr (fun z => ε ≤ |X z - D.E X|)
        = ∑ z, D.p z * (ε ^ 2 * (if ε ≤ |X z - D.E X| then (1 : ℝ) else 0)) := by
      unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun z _ => by ring)
    have hrhs : D.Var X = ∑ z, D.p z * (X z - D.E X) ^ 2 := rfl
    rw [hlhs, hrhs]
    refine hmono Finset.univ _ _ (fun z _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (D.p_nonneg z)
    by_cases hz' : ε ≤ |X z - D.E X|
    · simp only [hz', if_true, mul_one]
      rw [← sq_abs (X z - D.E X)]
      exact pow_le_pow_left₀ hε.le hz' 2
    · simp only [hz', if_false, mul_zero]
      exact sq_nonneg _
  rw [le_div_iff₀ hε2, mul_comm]
  exact hcore


end FiniteDesign
end DesignBased
end Experimentation
end Causalean
