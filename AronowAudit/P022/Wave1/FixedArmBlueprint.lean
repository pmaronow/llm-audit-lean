import AronowAudit.P022.Wave1.RandomizationVarianceBlueprint

/-!
# P022-T10: fixed-arm variance limit with eventual arm sizes

The fixed arm-size equalities are required eventually. Requiring them in every
row would force `m = k = 2`, because row `0` has `N = 4` and a valid design has
`m, k ≥ 2` and `m + k ≤ N`. Eventual equalities allow arbitrary fixed `m, k ≥ 2`
as on p. 852.

With `v1, v0` the divisor-`N` marginal variances and `c` their covariance,
equation (2) for `trueVariance` gives
`V_N - (v1/m + v0/k) = [2c - (1-1/m) v1 - (1-1/k) v0]/(N-1)`.
The identity `independent_means_remainder` and the bound
`|c| ≤ √(v1 v0) ≤ M` from `finite_covariance_cauchy` bound the error by
`4M/(N-1) = 4M/(q+3) → 0`.
-/

set_option autoImplicit false

namespace AronowAudit.P022.Wave1.FixedArm

open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- P022-T10: eventual fixed arm sizes and uniformly bounded marginal variances
make the remainder of the actual randomization variance vanish
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

/-- Uniform algebraic error bound for the right-hand side of (2). Both
coefficients 1-1/m and 1-1/k lie in [0,1], so `|c| ≤ √(v1 v0) ≤ M`
bounds the absolute numerator by 2M+M+M=4M. Apply
`AronowAudit.P022.independent_means_remainder` and then
`div_le_div_of_nonneg_right` with `N - 1 ≥ 1`. -/
def N1 : Prop :=
  ∀ (N m k : ℕ) (v1 v0 c M : ℝ), 2 ≤ m → 2 ≤ k → 2 ≤ N →
    0 ≤ v1 → v1 ≤ M → 0 ≤ v0 → v0 ≤ M → |c| ≤ Real.sqrt (v1 * v0) →
    |varianceExpression N m k v1 v0 c - (v1 / m + v0 / k)| ≤ 4 * M / ((N : ℝ) - 1)

/-- Finite variances are nonnegative. -/
theorem finiteVariance_nonneg' {N : ℕ} (v : Fin N → ℝ) : 0 ≤ finiteVariance v :=
  Finset.expect_nonneg (fun _ _ => sq_nonneg _)

/-- Intersect the eventual arm equalities, apply (2) and `N1`, and squeeze
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
