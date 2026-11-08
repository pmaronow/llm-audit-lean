import SAP.P008b.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b

open scoped BigOperators
open MeasureTheory Filter

noncomputable section

/-- Circle marginalization, node-effect and AMR integrals, and the sixteen-assignment design. -/
def T25Statement : Prop :=
  (∀ (N : ℕ) (P : SpatialModel N) (Q : FiniteLaw (Assignment N)) (i : Fin N) (d : ℝ),
    P.validCircle i d →
    (∀ b, P.m Q i b d = P.average i d (P.marginalY Q i b)) ∧
    P.nodeEffect Q i d = P.average i d (P.pointEffect Q i)) ∧
  (∀ (N : ℕ) (P : SpatialModel N) (Q : FiniteLaw (Assignment N)) (d : ℝ),
    0 < N → (∀ i, P.validCircle i d) →
    P.amr Q d = (N : ℝ)⁻¹ * ∑ i, P.average i d (P.pointEffect Q i)) ∧
  (∀ (Y : Assignment 4 → ℝ) (i : Fin 4) (b : Bool),
    marginal (uniformLaw (Assignment 4)) Y i b =
      (1 / 8 : ℝ) * ∑ z ∈ Finset.univ.filter (fun z => z i = b), Y z) ∧
  (∀ (Y : Assignment 4 → ℝ) (i : Fin 4),
    marginal (uniformLaw (Assignment 4)) Y i true -
        marginal (uniformLaw (Assignment 4)) Y i false =
      (1 / 8 : ℝ) * (∑ z ∈ Finset.univ.filter (fun z => z i = true), Y z) -
      (1 / 8 : ℝ) * (∑ z ∈ Finset.univ.filter (fun z => z i = false), Y z))

/-- Sharp-null vanishing on genuine averages and the finite cancelling witness. -/
def T26Statement : Prop :=
  (∀ (N : ℕ) (P : SpatialModel N), 0 < N → MeasurableSet P.field →
    P.sharpNull → ∀ Q : FiniteLaw (Assignment N),
    (∀ i x, x ∈ P.field → P.pointEffect Q i x = 0) ∧
    (∀ i d, P.validCircle i d → P.nodeEffect Q i d = 0) ∧
    (∀ d, (∀ i, P.validCircle i d) → P.amr Q d = 0)) ∧
  ((0 : ℚ) ∈ ({-1, 0, 1} : Finset ℚ) ∧
    (realLineCircle {-1, 0, 1} ![0] 0 0).card = 1 ∧
    (realLineCircle {-1, 0, 1} ![0] 0 1).card = 2 ∧
    (∀ (Q : FiniteLaw (Assignment 1)) (d : ℝ),
      (realLineCircle {-1, 0, 1} ![0] 0 d).Nonempty →
      finiteAMR Q (fun i z => realLineM {-1, 0, 1} ![0] cancellingOutcome i d z) = 0) ∧
    cancellingOutcome 1 ![true] ≠ cancellingOutcome 1 ![false])

/-- Additive and homogeneous coefficients identified by point, circle and node averages. -/
def T27Statement : Prop :=
  (∀ (N : ℕ) (P : SpatialModel N) (Q : FiniteLaw (Assignment N))
      (base : Plane → ℝ) (g : Fin N → Plane → ℝ),
    (∀ x ∈ P.field, ∀ z, P.Y x z = additiveOutcome base g x z) →
    (∀ i x, x ∈ P.field → P.pointEffect Q i x = g i x) ∧
    (∀ d, 0 < N → MeasurableSet P.field → (∀ i, P.validCircle i d) →
      (∀ i, P.nodeEffect Q i d = P.average i d (g i)) ∧
      P.amr Q d = (N : ℝ)⁻¹ * ∑ i, P.average i d (g i))) ∧
  (∀ (N : ℕ) (P : SpatialModel N) (Q : FiniteLaw (Assignment N))
      (base : Plane → ℝ) (g : ℝ → ℝ),
    (∀ x ∈ P.field, ∀ z, P.Y x z = additiveOutcome base
      (fun i x => g (dist (P.node i) x)) x z) →
    (∀ i x, x ∈ P.field → P.pointEffect Q i x = g (dist (P.node i) x)) ∧
    (∀ d, 0 < N → MeasurableSet P.field → (∀ i, P.validCircle i d) →
      (∀ i, P.nodeEffect Q i d = g d) ∧ P.amr Q d = g d))

/-- Only the audit's sufficient consistency theorem, with explicit empty-arm completion. -/
def T28Statement : Prop :=
  ∀ (Q : ∀ n, FiniteLaw (Assignment (n + 1)))
      (M : ∀ n, Fin (n + 1) → Assignment (n + 1) → ℝ)
      (p H exceptional : ℝ) (D : ℕ),
    0 < p → p < 1 → 0 ≤ H →
    (∀ n, commonBernoulli (Q n) p) →
    (∀ n i z, |M n i z| ≤ H) →
    (∀ n, boundedPairDependency (Q n) (M n) D) →
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => (Q n).prob (fun z => ε <
        |completedHajek (M n) exceptional z - finiteAMR (Q n) (M n)|))
      atTop (nhds 0)

end

end SAP.P008b
