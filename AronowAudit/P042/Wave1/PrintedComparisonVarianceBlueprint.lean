import AronowAudit.P042.Wave1.SixAtomicBlueprint

/-!
# Blueprint: refutation of `AronowAudit.P042.printed_comparison_variance` (P042-T5)

Record: P042-T5 / `AronowAudit.P042.printed_comparison_variance`; resolution `refute`.
Frozen contract (P042_Turnout.lean:737): for every probability space, finite index type,
nonempty disjoint pools `N`, `A`, effects in L² with positive variances,
`Var(pooled_N - pooled_A) = (∑_{j∈N} v_j⁻¹)⁻¹ + (∑_{j∈A} v_j⁻¹)⁻¹`.

`Target` is the negation of exactly that contract with `Ω ι : Type` (universe 0); the
`example` after it checks by `Iff.rfl` that it is the negation of the frozen declaration's
type at universes `0, 0`.

Witness (paper proof, record 1): `Ω = SixΩ`, `μ = sixMeasure`, `ι = Fin 2`, `D = sixD`,
`N = {0}`, `A = {1}`. The within-pool weights are `(1,0)` and `(0,1)`, so the left side is
`Var(D0 - D1) = 3/10 + 3/10 - 2·3/20 = 3/10`; the asserted right side is `3/10 + 3/10 = 3/5`.

Nodes: `SixAtomic.N1`, `SixAtomic.N2` (shared) and `N3` below. Writers prove
`theorem n3_proof : N3` in `AronowAudit/P042/Wave1/PrintedComparisonVariance/N3.lean`.
-/

set_option autoImplicit false

namespace AronowAudit.P042.Wave1.PrintedComparisonVariance

open AronowAudit.P042 AronowAudit.P042.Wave1.SixAtomic MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The frozen statement to be resolved: the negation of the exact recorded contract
`printed_comparison_variance` (universes 0, 0). -/
def Target : Prop :=
  ¬ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (N A : Finset ι),
    N.Nonempty → A.Nonempty → Disjoint N A →
    ∀ (D : ι → Ω → ℝ), (∀ j, MemLp (D j) 2 μ) → (∀ j, 0 < variance (D j) μ) →
      let v := fun j => variance (D j) μ
      variance (fun ω => pooled (subsetWeight N v) D ω - pooled (subsetWeight A v) D ω) μ =
        (∑ j ∈ N, (v j)⁻¹)⁻¹ + (∑ j ∈ A, (v j)⁻¹)⁻¹

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration, universes
0, 0). Only the frozen theorem's *type* is read; its `sorry` proof is never used. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P042.printed_comparison_variance.{0, 0}) :=
  Iff.rfl

/-- **Node N3** (paper proof, record 1, last paragraph: "the sole coefficient in each pool
is (10/3)/(10/3)=1, with zero coefficient outside that pool. The left side is
Var(D1-D2)=3/10+3/10-2(3/20)=3/10"). Under the shared nodes, the actual variance of the
difference of the singleton-pool precision-weighted means is `3/10`. Suggested route:
`subsetWeight {0} v = (1,0)`, `subsetWeight {1} v = (0,1)` since `v j = 3/10 > 0`, so the
difference is `sixD 0 - sixD 1` pointwise; then `difference_variance`. -/
def N3 : Prop :=
  SixAtomic.N1 → SixAtomic.SixMoments →
    variance (fun ω =>
        pooled (subsetWeight ({0} : Finset (Fin 2)) (fun j => variance (sixD j) sixMeasure)) sixD ω -
        pooled (subsetWeight ({1} : Finset (Fin 2)) (fun j => variance (sixD j) sixMeasure)) sixD ω)
      sixMeasure = 3/10

/-- The nodes suffice: specialize the frozen contract to the six-voter witness with the
singleton pools and compare `3/10` with `3/10 + 3/10 = 3/5`. -/
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

/-- Nonvacuity record: the witness satisfies every hypothesis of the frozen contract. -/
example (h1 : SixAtomic.N1) (h2 : SixAtomic.N2) :
    IsProbabilityMeasure sixMeasure ∧ ({0} : Finset (Fin 2)).Nonempty ∧
      ({1} : Finset (Fin 2)).Nonempty ∧ Disjoint ({0} : Finset (Fin 2)) {1} ∧
      (∀ j, MemLp (sixD j) 2 sixMeasure) ∧ (∀ j, 0 < variance (sixD j) sixMeasure) := by
  obtain ⟨hL2, hv0, hv1, -⟩ := h2 h1
  refine ⟨h1.1, by simp, by simp, by decide, hL2, ?_⟩
  intro j
  fin_cases j
  · simp only [Fin.zero_eta, hv0]; norm_num
  · simp only [Fin.mk_one, hv1]; norm_num

end

end AronowAudit.P042.Wave1.PrintedComparisonVariance
