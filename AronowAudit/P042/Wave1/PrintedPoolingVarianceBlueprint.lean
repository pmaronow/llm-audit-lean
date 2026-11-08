import AronowAudit.P042.Wave1.SixAtomicBlueprint

/-!
# Blueprint: refutation of `AronowAudit.P042.printed_pooling_variance` (P042-T5)

Record: P042-T5 / `AronowAudit.P042.printed_pooling_variance`; resolution `refute`.
Frozen contract (P042_Turnout.lean:700): for every probability space, `0 < J`, effects
`D : Fin J → Ω → ℝ` in L² with positive variances,
`Var(pooled (normalizedWeight v) D) = (totalWeight v)⁻¹` where `v j = Var (D j)`.

`Target` is the negation of exactly that contract, with `Ω : Type` (universe 0); the
universe-polymorphic frozen theorem would in particular give its universe-0 instance, so
this negation refutes it. The `example` after `Target` checks by `Iff.rfl` that `Target`
is definitionally the negation of the frozen declaration's type at universe 0.

Witness (paper proof, record 2): `Ω = SixΩ`, `μ = sixMeasure`, `J = 2`, `D = sixD`.
Both marginal variances are `3/10`, so `W = 20/3`, both normalized weights are `1/2`,
the pooled variance is `(3/10 + 3/10 + 2·3/20)/4 = 9/40`, while `W⁻¹ = 3/20`.

Nodes: `SixAtomic.N1`, `SixAtomic.N2` (shared, see `SixAtomicBlueprint`) and `N3` below.
Writers prove `theorem n3_proof : N3` in
`AronowAudit/P042/Wave1/PrintedPoolingVariance/N3.lean`.
-/

set_option autoImplicit false

namespace AronowAudit.P042.Wave1.PrintedPoolingVariance

open AronowAudit.P042 AronowAudit.P042.Wave1.SixAtomic MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The frozen statement to be resolved: the negation of the exact recorded contract
`printed_pooling_variance` (universe 0). -/
def Target : Prop :=
  ¬ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {J : ℕ},
    0 < J → ∀ (D : Fin J → Ω → ℝ), (∀ j, MemLp (D j) 2 μ) → (∀ j, 0 < variance (D j) μ) →
      variance (pooled (normalizedWeight (fun j => variance (D j) μ)) D) μ =
        (totalWeight (fun j => variance (D j) μ))⁻¹

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration, universe 0).
This only reads the frozen theorem's *type*; its `sorry` proof is never used. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P042.printed_pooling_variance.{0}) := Iff.rfl

/-- **Node N3** (paper proof, record 2, last paragraph: "both normalized weights are 1/2.
The pooled random variable is (D1+D2)/2, with variance [3/10+3/10+2(3/20)]/4=9/40").
Under the shared nodes, the actual `ProbabilityTheory.variance` of the precision-pooled
six-voter effect is `9/40`. Suggested route: `normalizedWeight` of `(3/10,3/10)` is `1/2`
(as in `six_counterexample`), then `pooled_variance` and `covariance_self`, or the
finite-average integral of `SixAtomic.N1` together with `six_moments`. -/
def N3 : Prop :=
  SixAtomic.N1 → SixAtomic.SixMoments →
    variance (pooled (normalizedWeight (fun j => variance (sixD j) sixMeasure)) sixD)
      sixMeasure = 9/40

/-- The nodes suffice: specialize the frozen contract to the six-voter witness and compare
`9/40` with `(20/3)⁻¹ = 3/20`. -/
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

/-- Nonvacuity record: the witness satisfies every hypothesis of the frozen contract
(given the shared nodes), so the refutation is not vacuous. -/
example (h1 : SixAtomic.N1) (h2 : SixAtomic.N2) :
    IsProbabilityMeasure sixMeasure ∧ 0 < (2 : ℕ) ∧ (∀ j, MemLp (sixD j) 2 sixMeasure) ∧
      (∀ j, 0 < variance (sixD j) sixMeasure) := by
  obtain ⟨hL2, hv0, hv1, -⟩ := h2 h1
  refine ⟨h1.1, by norm_num, hL2, ?_⟩
  intro j
  fin_cases j
  · simp only [Fin.zero_eta, hv0]; norm_num
  · simp only [Fin.mk_one, hv1]; norm_num

end

end AronowAudit.P042.Wave1.PrintedPoolingVariance
