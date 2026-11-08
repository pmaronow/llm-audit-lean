import AronowAudit.P022.P022_Variance

/-!
# Blueprint (shared): the actual randomization variance, equation (2) of P022

Shared by P022-T10 (`FixedArmBlueprint`) and P022-T13 (`SharpBoundsBlueprint`); see also
P022-T17 (deferred), which needs the same identity.

`Target` is equation (2), p. 851, for the *independently defined* finite randomization
variance `trueVariance` (a centred square averaged over all permutations), not the
asserted formula by definition.  It is the second conjunct of the P022-T13 contract.

Paper proof (map-P022 REPORT.md, record 9, step 1 "ACTUAL RANDOMIZATION MOMENTS"): at one
position a uniform permutation is uniform on the units; at two distinct positions it is
uniform on ordered pairs of distinct units, so
`E[a(π s) b(π t)] = ((Σa)(Σb) - Σ a_i b_i) / (N(N-1))` for `s ≠ t`.  Writing the centred
estimator as a position-linear statistic and expanding its square gives (2).

Writers prove `theorem nk_proof : Nk` in
`AronowAudit/P022/Wave1/RandomizationVariance/Nk.lean`.
-/

set_option autoImplicit false

namespace AronowAudit.P022.Wave1.RandomizationVariance

open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators

noncomputable section

/-- Position coefficient of the treated mean: `1/m` on positions `0,…,m-1`, else `0`. -/
def treatCoef (d : Design) (s : Fin d.N) : ℝ :=
  if s.val < d.m then 1 / (d.m : ℝ) else 0

/-- Position coefficient of minus the control mean: `-1/k` on positions `m,…,m+k-1`. -/
def ctrlCoef (d : Design) (s : Fin d.N) : ℝ :=
  if d.m ≤ s.val ∧ s.val < d.m + d.k then -(1 / (d.k : ℝ)) else 0

/-- **Target (shared; P022-T13 second conjunct).** Equation (2), p. 851, for the actual
finite randomization variance of `τ̂_N`. -/
def Target : Prop :=
  ∀ (d : Design) (y1 y0 : Fin d.N → ℝ),
    trueVariance d y1 y0 = varianceExpression d.N d.m d.k
      (finiteVariance y1) (finiteVariance y0) (finiteCovariance y1 y0)

/-- **Node N1** (map record 9, step 1: "for distinct positions s,t and distinct units i,j,
there are exactly (N-2)! permutations with π(s)=i, π(t)=j ... This also follows by
permutation invariance and summing over distinct images, avoiding factorial division").
One- and two-position moments of a uniform permutation.
Suggested route (no factorials): for `s ≠ t`, `Σ_t' E[a(πs) b(πt')] = E[a(πs)]·Σb = N μ_a μ_b`;
the `t' = s` term is `μ_{ab}` (`permutation_eval_mean` applied to `a*b`); the remaining
`N-1` terms are equal, by reindexing `π ↦ π * swap t t'` (which fixes `s`), exactly as in
the proof of `AronowAudit.P022.permutation_eval_mean`.  Shortcut: the vendored
`StatLean.HypothesisTesting.avg_perm_apply_pair` (import
`AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.PermutationMarginals`) already
gives the two-position marginal as the uniform average over `offDiag`. -/
def N1 : Prop :=
  ∀ {N : ℕ} (a b : Fin N → ℝ) (s t : Fin N),
    (s = t → (𝔼 π : Equiv.Perm (Fin N), a (π s) * b (π t)) =
        finiteMean (fun i => a i * b i)) ∧
    (s ≠ t → (𝔼 π : Equiv.Perm (Fin N), a (π s) * b (π t)) =
        ((N : ℝ) * finiteMean a * finiteMean b - finiteMean (fun i => a i * b i)) /
          ((N : ℝ) - 1))

/-- **Node N2** (map record 9, step 1: "Put u_i=y1_i-mu1, v_i=y0_i-mu0 ... the treated mean
... the control mean"). The centred estimator is a position-linear statistic of the
centred outcomes. Pure finite algebra: reindex `Fin d.m` (resp. `Fin d.k`) into the first
`m` (resp. the next `k`) positions of `Fin d.N`, and use `Σ treatCoef = 1`,
`Σ ctrlCoef = -1` to absorb the population means. -/
def N2 : Prop :=
  ∀ (d : Design) (y1 y0 : Fin d.N → ℝ) (π : Assignment d),
    estimatedEffect d y1 y0 π - averageEffect d y1 y0 =
      ∑ s : Fin d.N, (treatCoef d s * (y1 (π s) - finiteMean y1) +
        ctrlCoef d s * (y0 (π s) - finiteMean y0))

/-- **Node N3** (map record 9, step 1: "Equal-position second moments are v1,v0,c and
unequal-position mixed moments are -v1/(N-1), -v0/(N-1), -c/(N-1)"). Second moment of an
arbitrary position-linear statistic of two centred arrays under a uniform permutation.
Expand the square as a double sum over positions, exchange `𝔼` with the finite sums, and
apply `N1` to each term (diagonal vs off-diagonal); `finiteMean u = 0` kills `N μ_u μ_v`.
Stated as a consequence of `N1`. -/
def N3 : Prop :=
  N1 → ∀ {N : ℕ} (u v α γ : Fin N → ℝ), 2 ≤ N → finiteMean u = 0 → finiteMean v = 0 →
    (𝔼 π : Equiv.Perm (Fin N), (∑ s, (α s * u (π s) + γ s * v (π s))) ^ 2) =
      finiteMean (fun i => u i ^ 2) *
          (∑ s, α s ^ 2 - ((∑ s, α s) ^ 2 - ∑ s, α s ^ 2) / ((N : ℝ) - 1)) +
        2 * finiteMean (fun i => u i * v i) *
          (∑ s, α s * γ s - ((∑ s, α s) * (∑ s, γ s) - ∑ s, α s * γ s) / ((N : ℝ) - 1)) +
        finiteMean (fun i => v i ^ 2) *
          (∑ s, γ s ^ 2 - ((∑ s, γ s) ^ 2 - ∑ s, γ s ^ 2) / ((N : ℝ) - 1))

/-- **Node N4** (map record 9, step 1: "the treated mean has variance ... all mk cross-arm
position pairs are distinct"). The five coefficient sums. Finite sums over a filtered
range of `Fin d.N`; uses `d.treatment_min`, `d.control_min`, `d.sample_le`. -/
def N4 : Prop :=
  ∀ d : Design,
    ∑ s, treatCoef d s = 1 ∧ ∑ s, treatCoef d s ^ 2 = 1 / (d.m : ℝ) ∧
    ∑ s, ctrlCoef d s = -1 ∧ ∑ s, ctrlCoef d s ^ 2 = 1 / (d.k : ℝ) ∧
    ∑ s, treatCoef d s * ctrlCoef d s = 0

/-- The centred array has mean zero (glue, proved here). -/
theorem finiteMean_centered {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ) :
    finiteMean (fun i => y i - finiteMean y) = 0 := by
  have : NeZero N := ⟨by omega⟩
  unfold finiteMean
  rw [Finset.expect_sub_distrib, Finset.expect_const Finset.univ_nonempty]
  ring

/-- **Assembly.** The nodes give equation (2) for every valid design. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) : Target := by
  intro d y1 y0
  have hN4 : 4 ≤ d.N := d.population_min
  have hm2 : 2 ≤ d.m := d.treatment_min
  have hk2 : 2 ≤ d.k := d.control_min
  have hunb := difference_in_means_unbiased d y1 y0
  have hsq : trueVariance d y1 y0 =
      𝔼 π : Equiv.Perm (Fin d.N), (∑ s : Fin d.N, (treatCoef d s * (y1 (π s) - finiteMean y1) +
        ctrlCoef d s * (y0 (π s) - finiteMean y0))) ^ 2 := by
    unfold trueVariance designVariance
    rw [hunb]
    unfold designExpectation
    apply Finset.expect_congr rfl
    intro π _
    rw [h2 d y1 y0 π]
  rw [hsq, h3 h1 (fun i => y1 i - finiteMean y1) (fun i => y0 i - finiteMean y0)
    (treatCoef d) (ctrlCoef d) (by omega) (finiteMean_centered (by omega) y1)
    (finiteMean_centered (by omega) y0)]
  obtain ⟨s1, s2, s3, s4, s5⟩ := h4 d
  rw [s1, s2, s3, s4, s5]
  change finiteVariance y1 * _ + 2 * finiteCovariance y1 y0 * _ + finiteVariance y0 * _ = _
  have hm0 : (d.m : ℝ) ≠ 0 := by exact_mod_cast (show d.m ≠ 0 by omega)
  have hk0 : (d.k : ℝ) ≠ 0 := by exact_mod_cast (show d.k ≠ 0 by omega)
  have hN1 : (d.N : ℝ) - 1 ≠ 0 := by
    have : (4 : ℝ) ≤ d.N := by exact_mod_cast hN4
    linarith
  unfold varianceExpression
  field_simp
  ring

end

end AronowAudit.P022.Wave1.RandomizationVariance
