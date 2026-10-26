import AronowAudit.P042.P042_Turnout

/-!
The probability space and moments of the six-voter shared-control
counterexample to the pooling and comparison variance assertions (P042-T5).

Every ordered pair `(T1, T2)` of disjoint two-voter treatment sets leaves the
remaining two voters as the shared control, each of the 90 allocations having
mass `1/90` (P042-T1 A; P042-E001). Voters `0,1,2` turn out and `3,4,5` do not,
under every arm. The effects are `D 0 = sixD1` (treatment 1 minus control)
and `D 1 = sixD2`.
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

/-- The atomic measure is a probability measure, and integration against it
is the finite average over the 90 allocations.
The cardinality is `six_design.1 : sixAllocations.card = 90`. -/
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

/-- Under `N1`, which supplies the finite-average integral, both effects are
in L², both variances are `3/10`, and the covariance is `3/20`.
The rational moments are `six_moments`; `MemLp.of_discrete` gives L². -/
def N2 : Prop :=
  N1 → SixMoments

end

end AronowAudit.P042.Wave1.SixAtomic
