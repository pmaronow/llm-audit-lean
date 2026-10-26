import AronowAudit.P042.Wave1.SixAtomicBlueprint

/-!
P042-T5: counterexample to the unrestricted pooling-variance assertion.

The assertion equates `Var(pooled (normalizedWeight v) D)` to `(totalWeight v)⁻¹`,
where `v j = Var (D j)`, for `0 < J` and effects `D : Fin J → Ω → ℝ` in L²
with positive variances on any probability space.
`Target` negates this assertion for `Ω : Type` (universe 0).

The witness uses `Ω = SixΩ`, `μ = sixMeasure`, `J = 2`, `D = sixD`.
Both marginal variances are `3/10`, so `W = 20/3`, both normalized weights are `1/2`,
the pooled variance is `(3/10 + 3/10 + 2·3/20)/4 = 9/40`, while `W⁻¹ = 3/20`.
-/

set_option autoImplicit false

namespace AronowAudit.P042.Wave1.PrintedPoolingVariance

open AronowAudit.P042 AronowAudit.P042.Wave1.SixAtomic MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Negation of the unrestricted pooling-variance assertion (universe 0). -/
def Target : Prop :=
  ¬ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {J : ℕ},
    0 < J → ∀ (D : Fin J → Ω → ℝ), (∀ j, MemLp (D j) 2 μ) → (∀ j, 0 < variance (D j) μ) →
      variance (pooled (normalizedWeight (fun j => variance (D j) μ)) D) μ =
        (totalWeight (fun j => variance (D j) μ))⁻¹

/-- Under the shared probability-law and moment hypotheses, the variance of
the precision-pooled six-voter effect is `9/40`. Both normalized weights are
`1/2`, so the pooled random variable is `(D1+D2)/2`, with variance
`[3/10 + 3/10 + 2·(3/20)]/4 = 9/40`. -/
def N3 : Prop :=
  SixAtomic.N1 → SixAtomic.SixMoments →
    variance (pooled (normalizedWeight (fun j => variance (sixD j) sixMeasure)) sixD)
      sixMeasure = 9/40

/-- Specializing the unrestricted assertion to the six-voter witness
contradicts `9/40 ≠ (20/3)⁻¹ = 3/20`. -/
theorem assemble (h1 : SixAtomic.N1) (h2 : SixAtomic.N2) (h3 : N3) : Target := by
  intro h
  have : IsProbabilityMeasure sixMeasure := h1.1
  obtain ⟨hL2, hv0, hv1, -⟩ := h2 h1
  have hpos : ∀ j, 0 < variance (sixD j) sixMeasure := by
    intro j
    fin_cases j
    · simp only [Fin.zero_eta, hv0]; norm_num
    · simp only [Fin.mk_one, hv1]; norm_num
  have key := h SixΩ sixMeasure (J := 2) (by norm_num) sixD hL2 hpos
  have htw : totalWeight (fun j => variance (sixD j) sixMeasure) = 20/3 := by
    simp only [totalWeight, precisionWeight, Fin.sum_univ_two, hv0, hv1]
    norm_num
  rw [h3 h1 (h2 h1), htw] at key
  norm_num at key

end

end AronowAudit.P042.Wave1.PrintedPoolingVariance
