import AronowAudit.P022.Wave1.RandomizationVarianceBlueprint

/-!
# Blueprint: P022-T10, fixed-arm variance limit with eventual arm sizes

Record: P022-T10 / `AronowAudit.P022.fixed_arm_variance_limit`; resolution `repair_and_prove`.

The frozen draft requires `(S.design q).m = m` and `(S.design q).k = k` for *every* row
`q`; since row `0` has `N = 4` and a valid design has `m, k ≥ 2`, `m + k ≤ N`, this forces
`m = k = 2`, excluding the arbitrary fixed `m, k ≥ 2` allowed on p. 852.  The repaired
contract (mapper record 8, accepted by both referees) replaces the all-row equalities by
eventual ones and keeps everything else verbatim.

Paper proof (map record 8): with `v1, v0` the divisor-`N` marginal variances and `c` their
covariance, equation (2) for the actual `trueVariance` (shared `RandomizationVariance`)
gives `V_N - (v1/m + v0/k) = [2c - (1-1/m) v1 - (1-1/k) v0]/(N-1)`
(`independent_means_remainder`, proved); `|c| ≤ √(v1 v0) ≤ M` (`finite_covariance_cauchy`,
proved), so the error is at most `4M/(N-1) = 4M/(q+3) → 0`.

Nodes: the shared `RandomizationVariance.N1`–`N4` and `N1` below.
Writers prove `theorem n1_proof : N1` in `AronowAudit/P022/Wave1/FixedArm/N1.lean`.
Final file: `AronowAudit/P022/Wave1/FixedArm.lean`, theorem
`AronowAudit.P022.Wave1.fixed_arm_variance_limit_eventually`.
-/

set_option autoImplicit false

namespace AronowAudit.P022.Wave1.FixedArm

open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- **Target (P022-T10, repaired).** Eventual fixed arm sizes and uniformly bounded
marginal variances make the remainder of the actual randomization variance vanish
(Section 2, p. 852). -/
def Target : Prop :=
  ∀ (S : ExperimentSequence) (m k : ℕ),
    (∀ᶠ q : ℕ in atTop, (S.design q).m = m) →
    (∀ᶠ q : ℕ in atTop, (S.design q).k = k) →
    (∃ M : ℝ, ∀ q, finiteVariance (rowOutcomes S true q) ≤ M ∧
      finiteVariance (rowOutcomes S false q) ≤ M) →
    Tendsto (fun q => trueVariance (S.design q)
      (rowOutcomes S true q) (rowOutcomes S false q) -
      (finiteVariance (rowOutcomes S true q) / m +
       finiteVariance (rowOutcomes S false q) / k)) atTop (𝓝 0)

/-- Fidelity check: `Target` has exactly the frozen conclusion; the frozen all-row
hypotheses imply the new eventual ones, so `Target` implies the frozen draft. -/
example (h : Target) : type_of% @AronowAudit.P022.fixed_arm_variance_limit :=
  fun S m k hm hk hb => h S m k (Eventually.of_forall hm) (Eventually.of_forall hk) hb

/-- **Node N1** (map record 8: "Both coefficients 1-1/m and 1-1/k lie in [0,1], so the
absolute numerator is at most 2M+M+M=4M"). Uniform algebraic error bound for the right-hand
side of (2). Use `AronowAudit.P022.independent_means_remainder`, then
`|c| ≤ √(v1 v0) ≤ M` (`Real.sqrt_le_sqrt`, `Real.sqrt_mul_self`), and
`div_le_div_of_nonneg_right` with `N - 1 ≥ 1`. -/
def N1 : Prop :=
  ∀ (N m k : ℕ) (v1 v0 c M : ℝ), 2 ≤ m → 2 ≤ k → 2 ≤ N →
    0 ≤ v1 → v1 ≤ M → 0 ≤ v0 → v0 ≤ M → |c| ≤ Real.sqrt (v1 * v0) →
    |varianceExpression N m k v1 v0 c - (v1 / m + v0 / k)| ≤ 4 * M / ((N : ℝ) - 1)

/-- Finite variances are nonnegative (glue). -/
theorem finiteVariance_nonneg' {N : ℕ} (v : Fin N → ℝ) : 0 ≤ finiteVariance v :=
  Finset.expect_nonneg (fun _ _ => sq_nonneg _)

/-- **Assembly.** Intersect the eventual arm equalities, apply (2) and `N1`, and squeeze
with `4M/(q+3)`. -/
theorem assemble (r1 : RandomizationVariance.N1) (r2 : RandomizationVariance.N2)
    (r3 : RandomizationVariance.N3) (r4 : RandomizationVariance.N4) (h1 : N1) : Target := by
  intro S m k hm hk hb
  have hRV := RandomizationVariance.assemble r1 r2 r3 r4
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := le_trans (finiteVariance_nonneg' _) (hM 0).1
  have hden : Tendsto (fun q : ℕ => ((q : ℝ) + 4) - 1) atTop atTop := by
    apply tendsto_atTop_add_const_right
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun q : ℕ => 4 * M / (((q : ℝ) + 4) - 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hm, hk] with q hmq hkq
  rw [Real.norm_eq_abs, hRV]
  have hm2 : 2 ≤ m := hmq ▸ (S.design q).treatment_min
  have hk2 : 2 ≤ k := hkq ▸ (S.design q).control_min
  have hN : ((S.design q).N : ℝ) = (q : ℝ) + 4 := by exact_mod_cast S.size q
  have hb := h1 (S.design q).N m k (finiteVariance (rowOutcomes S true q))
    (finiteVariance (rowOutcomes S false q))
    (finiteCovariance (rowOutcomes S true q) (rowOutcomes S false q)) M hm2 hk2
    (by have := (S.design q).population_min; omega)
    (finiteVariance_nonneg' _) (hM q).1 (finiteVariance_nonneg' _) (hM q).2
    (finite_covariance_cauchy _ _)
  rw [hmq, hkq, ← hN]
  exact hb

end

end AronowAudit.P022.Wave1.FixedArm
