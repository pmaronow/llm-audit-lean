import AronowAudit.P018.P018_Audit

/-!
# P018-T28: refutation of the scalar specialization of both printed corollaries

In the fair-sign intercept model (`k = T(d) = w_d = 1`, `X = 1`,
`Y_ij = U_i + U_j`), the literal conclusions of Corollaries 1–2
(pp. 567–568, 575–576) use the missing-sum target `4/D`:
(i) `N Var(β̂) - 4/D → 0` and (ii) `N V̂ - 4/D → 0` in probability.
`Target` is the negation of that conjunction.

Each unit is in `N-1` dyads, so `β̂ = (N-1) S / D = 2S/N` with
`S = Σ_i U_i`, and `Var S = N`; hence `N Var(β̂) = 4` for every
`N ≥ 2` while `4/D → 0`. The first sequence therefore tends to `4`, not `0`.
Failure of conjunct (i) refutes the conjunction; (ii) is not needed.

This refutes the literal printed display, with an outer expectation where the dyad
sum belongs (finding P018-E004), specialized to a conformable scalar case.
It does not refute the intended corollaries; their corrected forms are P018-T10/T12.
-/

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.PrintedScalarCorollaries

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

noncomputable section

/-- **Target (P018-T28, scalar).** Negation of the printed scalar corollary claims. -/
def Target : Prop :=
  ¬ (Tendsto (fun N : ℕ => (N : ℝ) * ProbabilityTheory.variance
      (fun ω => sampleOLS (design signKernel ω) (response signKernel ω) 0)
      (unitSampleLaw signKernel N) - 4 / Dreal N) atTop (𝓝 0) ∧
    inProbability (unitSampleLaw signKernel) (fun N ω =>
      (N : ℝ) * (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 -
        4 / Dreal N))

/-! ## Component propositions -/

/-- For `N ≥ 2`, the fitted intercept equals `2S/N` for every sign sample,
where `S` is the sum of its signs. -/
def N1 : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ ω : Fin N → Bool,
    sampleOLS (design signKernel ω) (response signKernel ω) 0 =
      (2 / (N : ℝ)) * ∑ i, signValue (ω i)

/-- The sum `S` of `N` independent fair signs has variance `N` under the product sample law. -/
def N2 : Prop :=
  ∀ (N : ℕ), ProbabilityTheory.variance (fun ω : Fin N → Bool => ∑ i, signValue (ω i))
    (unitSampleLaw signKernel N) = N

/-! ## Assembly -/

/-- `D_N → ∞`, hence `4/D_N → 0`. -/
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

/-- The two component propositions imply the negation of the printed conjunction:
the first printed sequence is eventually `4 - 4/D`. -/
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
