import AronowAudit.P042.Wave1.SixAtomicBlueprint

/-!
P042-T5: counterexample to the unrestricted comparison-variance assertion.

The assertion equates `Var(pooled_N - pooled_A)` to
`(∑_{j∈N} v_j⁻¹)⁻¹ + (∑_{j∈A} v_j⁻¹)⁻¹` for nonempty disjoint pools `N`, `A`
and effects in L² with positive variances on any probability space.
`Target` negates this assertion for `Ω ι : Type` (universe 0).

The witness uses `Ω = SixΩ`, `μ = sixMeasure`, `ι = Fin 2`, `D = sixD`,
`N = {0}`, `A = {1}`. The within-pool weights are `(1,0)` and `(0,1)`, so the left side is
`Var(D0 - D1) = 3/10 + 3/10 - 2·3/20 = 3/10`; the asserted right side is `3/10 + 3/10 = 3/5`.
-/

set_option autoImplicit false

namespace AronowAudit.P042.Wave1.PrintedComparisonVariance

open AronowAudit.P042 AronowAudit.P042.Wave1.SixAtomic MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Negation of the unrestricted comparison-variance assertion (universes 0, 0). -/
def Target : Prop :=
  ¬ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (N A : Finset ι),
    N.Nonempty → A.Nonempty → Disjoint N A →
    ∀ (D : ι → Ω → ℝ), (∀ j, MemLp (D j) 2 μ) → (∀ j, 0 < variance (D j) μ) →
      let v := fun j => variance (D j) μ
      variance (fun ω => pooled (subsetWeight N v) D ω - pooled (subsetWeight A v) D ω) μ =
        (∑ j ∈ N, (v j)⁻¹)⁻¹ + (∑ j ∈ A, (v j)⁻¹)⁻¹

/-- Under the shared probability-law and moment hypotheses, the variance of
the difference of the singleton-pool precision-weighted means is `3/10`.
The sole coefficient in each pool is `(10/3)/(10/3)=1`, with zero coefficient
outside that pool. Thus the difference is `sixD 0 - sixD 1` pointwise and
its variance is `3/10 + 3/10 - 2·(3/20) = 3/10`. -/
def N3 : Prop :=
  SixAtomic.N1 → SixAtomic.SixMoments →
    variance (fun ω =>
        pooled (subsetWeight ({0} : Finset (Fin 2)) (fun j => variance (sixD j) sixMeasure)) sixD ω -
        pooled (subsetWeight ({1} : Finset (Fin 2)) (fun j => variance (sixD j) sixMeasure)) sixD ω)
      sixMeasure = 3/10

/-- Specializing the unrestricted assertion to the six-voter witness with
singleton pools contradicts `3/10 ≠ 3/10 + 3/10 = 3/5`. -/
theorem assemble (h1 : SixAtomic.N1) (h2 : SixAtomic.N2) (h3 : N3) : Target := by
  intro h
  have : IsProbabilityMeasure sixMeasure := h1.1
  obtain ⟨hL2, hv0, hv1, -⟩ := h2 h1
  have hpos : ∀ j, 0 < variance (sixD j) sixMeasure := by
    intro j
    fin_cases j
    · simp only [Fin.zero_eta, hv0]; norm_num
    · simp only [Fin.mk_one, hv1]; norm_num
  have key := h SixΩ sixMeasure (Fin 2) {0} {1} (by simp) (by simp) (by decide) sixD hL2 hpos
  simp only at key
  rw [h3 h1 (h2 h1)] at key
  simp only [Finset.sum_singleton, hv0, hv1] at key
  norm_num at key

end

end AronowAudit.P042.Wave1.PrintedComparisonVariance
