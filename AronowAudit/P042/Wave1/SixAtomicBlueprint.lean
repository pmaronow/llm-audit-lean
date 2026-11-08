import AronowAudit.P042.P042_Turnout

/-!
# Shared blueprint nodes for the two P042-T5 refutations

Blueprint (Wave 1, group P042-P045). This module fixes the explicit probability space
on which both `printed_pooling_variance` and `printed_comparison_variance` fail, and the
two shared nodes (atomic-measure bridge, six-voter moments). Both record blueprints
`PrintedPoolingVarianceBlueprint` and `PrintedComparisonVarianceBlueprint` import it.

The space is the validators' six-voter shared-control randomization (P042-T1 A; P042-E001 v1,
"Exact finite-population counterexample"): every ordered pair `(T1, T2)` of disjoint
two-voter treatment sets, the remaining two voters forming the shared control, each of the
90 allocations having mass `1/90`. Voters `0,1,2` turn out and `3,4,5` do not, under every arm.
The effects are `D 0 = sixD1` (treatment 1 minus control) and `D 1 = sixD2`.

Writers: prove `theorem n1_proof : N1` in `AronowAudit/P042/Wave1/SixAtomic/N1.lean` and
`theorem n2_proof : N2` in `AronowAudit/P042/Wave1/SixAtomic/N2.lean`.
Never use the frozen false theorems `printed_pooling_variance` / `printed_comparison_variance`.
-/

set_option autoImplicit false

namespace AronowAudit.P042.Wave1.SixAtomic

open AronowAudit.P042 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Sample space of the six-voter witness: ordered pairs `(T1, T2)` of treatment sets.
A type synonym, so that the discrete measurable structure below cannot clash with any
library instance on products of finsets. -/
def SixΩ : Type := Finset (Fin 6) × Finset (Fin 6)

instance : Fintype SixΩ := inferInstanceAs (Fintype (Finset (Fin 6) × Finset (Fin 6)))
instance : DecidableEq SixΩ := inferInstanceAs (DecidableEq (Finset (Fin 6) × Finset (Fin 6)))

/-- The discrete σ-algebra: every subset of the finite sample space is an event. -/
instance : MeasurableSpace SixΩ := ⊤

instance : DiscreteMeasurableSpace SixΩ := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Uniform law on the 90 labelled complete randomizations (P042-T1 A):
`μ = 90⁻¹ • ∑_{a ∈ sixAllocations} δ_a`. Allocations outside `sixAllocations` are null. -/
def sixMeasure : Measure SixΩ :=
  (90 : ℝ≥0∞)⁻¹ • ∑ a ∈ sixAllocations, (Measure.dirac (a : SixΩ) : Measure SixΩ)

/-- The two study effects of P042-T1 A as real random variables:
`D 0 = sixD1` (arm 1 minus shared control), `D 1 = sixD2` (arm 2 minus shared control). -/
def sixD : Fin 2 → SixΩ → ℝ := fun j a =>
  if j = 0 then ((sixD1 a : ℚ) : ℝ) else ((sixD2 a : ℚ) : ℝ)

/-- **Node SixAtomic.N1** (paper proof, records 1-2, paragraph "The required bridge from
those rational finite moments to ProbabilityTheory.variance"): the atomic measure is a
probability measure, and integration against it is the finite average over the 90
allocations. Uses `six_design.1 : sixAllocations.card = 90`. -/
def N1 : Prop :=
  IsProbabilityMeasure sixMeasure ∧
    ∀ f : SixΩ → ℝ, ∫ ω, f ω ∂sixMeasure = (∑ a ∈ sixAllocations, f a) / 90

/-- Content of node `N2`: both effects are in L², both marginal variances are `3/10`, and
the shared-control covariance is `3/20` (all as `ProbabilityTheory` quantities). -/
def SixMoments : Prop :=
  (∀ j, MemLp (sixD j) 2 sixMeasure) ∧
    variance (sixD 0) sixMeasure = 3/10 ∧
    variance (sixD 1) sixMeasure = 3/10 ∧
    covariance (sixD 0) (sixD 1) sixMeasure = 3/20

/-- **Node SixAtomic.N2** (paper proof, records 1-2, first two paragraphs: `Var D1 = Var D2 =
3/10`, `Cov(D1,D2) = 3/20`, plus "every function on this finite space is measurable and
bounded, hence belongs to L²"). Stated under `N1`, which supplies the finite-average
integral; the rational values are `six_moments`; `MemLp.of_discrete` gives L². -/
def N2 : Prop :=
  N1 → SixMoments

/-- Sanity check of the encoding: `sixD 0` and `sixD 1` are the casts of the two
recorded contrasts. -/
example (a : SixΩ) : sixD 0 a = ((sixD1 a : ℚ) : ℝ) ∧ sixD 1 a = ((sixD2 a : ℚ) : ℝ) :=
  ⟨rfl, rfl⟩

end

end AronowAudit.P042.Wave1.SixAtomic
