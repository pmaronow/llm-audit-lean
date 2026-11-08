import AronowAudit.P018.P018_Audit

/-!
# Blueprint: P018-T28, refutation of the scalar specialization of both printed corollaries

Record: P018-T28 / `AronowAudit.P018.printed_corollaries_scalar`; resolution `refute`.

Frozen contract (P018_Audit.lean:1617): in the fair-sign intercept model
(`k = T(d) = w_d = 1`, `X = 1`, `Y_ij = U_i + U_j`) both printed conclusions of
Corollaries 1–2 (pp. 567–568, 575–576) hold with the literal missing-sum target `4/D`:
(i) `N Var(β̂) - 4/D → 0` and (ii) `N V̂ - 4/D → 0` in probability.  `Target` is the
negation of that closed conjunction, checked below by `Iff.rfl`.

Paper proof (map record 6, accepted by both referees): each unit is in `N-1` dyads, so
`β̂ = (N-1) S / D = 2S/N` with `S = Σ_i U_i`, and `Var S = N`; hence `N Var(β̂) = 4` for
every `N ≥ 2` while `4/D → 0`, so the first sequence tends to `4`, not `0`.  Failure of
conjunct (i) refutes the conjunction; (ii) is not needed.

Scope caution for the orchestrator: this refutes the *literal* printed display (an outer
expectation where the dyad sum belongs: audit finding P018-E004, rated Minor), specialized
to a conformable scalar case.  It does not refute the intended corollaries; their
corrected forms are P018-T10/T12 (record 2 of this group is the weighted one).

Nodes `N1`, `N2`.  Writers prove `theorem nk_proof : Nk` in
`AronowAudit/P018/Wave1/PrintedScalarCorollaries/Nk.lean`.
Final file: `AronowAudit/P018/Wave1/PrintedScalarCorollaries.lean`, theorem
`AronowAudit.P018.Wave1.printed_corollaries_scalar_refuted`.
-/

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.PrintedScalarCorollaries

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

noncomputable section

/-- **Target (P018-T28, scalar).** Exact negation of `printed_corollaries_scalar`. -/
def Target : Prop :=
  ¬ (Tendsto (fun N : ℕ => (N : ℝ) * ProbabilityTheory.variance
      (fun ω => sampleOLS (design signKernel ω) (response signKernel ω) 0)
      (unitSampleLaw signKernel N) - 4 / Dreal N) atTop (𝓝 0) ∧
    inProbability (unitSampleLaw signKernel) (fun N ω =>
      (N : ℝ) * (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 -
        4 / Dreal N))

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration). Only the
frozen theorem's *type* is read; its unfinished draft proof is never used. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P018.printed_corollaries_scalar) := Iff.rfl

/-! ## Nodes -/

/-- **Node N1** (map record 6: "For N≥2, the sample Gram is D=N(N-1)/2>0 ... Each unit
occurs in N-1 dyads, so beta_hat=(N-1)S/D=2S/N"). Deterministic OLS formula in the sign
model, for every sample.
Suggested route: `sampleGram (design signKernel ω) = !![Dreal N]` (a `1×1` matrix,
`number_of_dyads`, `Nat.cast_choose_two`); its inverse is `!![(Dreal N)⁻¹]`
(`Matrix.inv_def`, `Matrix.det_unique`); `Σ_d (U_first + U_second) = (N-1) Σ_i U_i`
(double counting: `Finset.sum_comm` over incidences, each unit lies in `N-1` dyads). -/
def N1 : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ ω : Fin N → Bool,
    sampleOLS (design signKernel ω) (response signKernel ω) 0 =
      (2 / (N : ℝ)) * ∑ i, signValue (ω i)

/-- **Node N2** (map record 6: "Independence and Var(U_i)=1 give Var(S)=N"). Variance of the
sum of `N` iid fair signs under the actual product law. Suggested route:
`ProbabilityTheory.iIndepFun_pi` (coordinates of `Measure.pi` are independent),
`ProbabilityTheory.IndepFun.variance_sum`, and `variance_def'` on the two-point law
`(PMF.uniformOfFintype Bool).toMeasure` (`PMF.integral_eq_sum`, `Fintype.sum_bool`). -/
def N2 : Prop :=
  ∀ (N : ℕ), ProbabilityTheory.variance (fun ω : Fin N → Bool => ∑ i, signValue (ω i))
    (unitSampleLaw signKernel N) = N

/-! ## Assembly -/

/-- `D_N → ∞`, hence `4/D_N → 0` (glue). -/
theorem four_div_D_tendsto : Tendsto (fun N : ℕ => 4 / Dreal N) atTop (𝓝 0) := by
  have hge : ∀ N : ℕ, (N : ℝ) - 1 ≤ Dreal N := by
    intro N
    unfold Dreal
    rcases Nat.lt_or_ge N 2 with h | h
    · interval_cases N <;> norm_num
    · have : (2 : ℝ) ≤ N := by exact_mod_cast h
      nlinarith
  have hlin : Tendsto (fun N : ℕ => (N : ℝ) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_mono hge hlin)

/-- **Assembly.** The nodes suffice: the first printed sequence is eventually `4 - 4/D`. -/
theorem assemble (h1 : N1) (h2 : N2) : Target := by
  rintro ⟨hA, -⟩
  have hev : ∀ᶠ N : ℕ in atTop, (N : ℝ) * ProbabilityTheory.variance
      (fun ω => sampleOLS (design signKernel ω) (response signKernel ω) 0)
      (unitSampleLaw signKernel N) - 4 / Dreal N = 4 - 4 / Dreal N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hfun : (fun ω : Fin N → Bool =>
        sampleOLS (design signKernel ω) (response signKernel ω) 0) =
        fun ω => (2 / (N : ℝ)) * ∑ i, signValue (ω i) := funext (h1 N hN)
    rw [hfun, ProbabilityTheory.variance_const_mul, h2 N]
    have hN0 : (N : ℝ) ≠ 0 := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    field_simp
    ring
  have h4 : Tendsto (fun N : ℕ => (4 : ℝ) - 4 / Dreal N) atTop (𝓝 (4 - 0)) :=
    tendsto_const_nhds.sub four_div_D_tendsto
  have h0 := tendsto_nhds_unique (hA.congr' hev) h4
  norm_num at h0

end

end AronowAudit.P018.Wave1.PrintedScalarCorollaries
