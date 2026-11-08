import Mathlib
import SAP.P025b.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

/-- The attainable set depends only on the ratio; at ratio one its box is a point. -/
def T18Statement : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (y : Fin n → ℝ) (α β α' β' : ℝ),
    0 < α → α ≤ β → β ≤ 1 → 0 < α' → α' ≤ β' → β' ≤ 1 →
    β/α = β'/α' →
    attainable y (fun _ => 1) α β = attainable y (fun _ => 1) α' β' ∧
    attainable y (fun _ => 1) α β = normAttainable y (fun _ => 1) (β/α) ∧
    lowerEndpoint y (fun _ => 1) α β = lowerEndpoint y (fun _ => 1) α' β' ∧
    upperEndpoint y (fun _ => 1) α β = upperEndpoint y (fun _ => 1) α' β' ∧
    (β/α = 1 →
      (∀ w : Fin n → ℝ, weightBox α β w ↔ w = fun _ => 1/α) ∧
      lowerEndpoint y (fun _ => 1) α β = populationMean y ∧
      upperEndpoint y (fun _ => 1) α β = populationMean y)

/-- Lemma 1's tied-weight conclusion, using the corrected lower first cut. -/
def T19Statement : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (y : Fin n → ℝ), Monotone y →
    ∀ (α β : ℝ), 0 < α → α ≤ β → β ≤ 1 →
    ∀ (kL kH : Fin n),
      lowerCut y (fun _ => 1) (β/α) kL → upperCut y (fun _ => 1) (β/α) kH →
      ∀ i j : Fin n, y i = y j →
        (1/β)*lowerWeights (β/α) kL.val i = (1/β)*lowerWeights (β/α) kL.val j ∧
        (1/β)*upperWeights (β/α) kH.val i = (1/β)*upperWeights (β/α) kH.val j

/-- The full binary attainable interval and its endpoints, including all degenerate cases. -/
def T20Statement : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (y : Fin n → ℝ), (∀ i, y i = 0 ∨ y i = 1) →
    ∀ (α β : ℝ), 0 < α → α ≤ β → β ≤ 1 →
    attainable y (fun _ => 1) α β =
      Set.Icc (binaryLower (populationMean y) (β/α)) (binaryUpper (populationMean y) (β/α)) ∧
    lowerEndpoint y (fun _ => 1) α β = binaryLower (populationMean y) (β/α) ∧
    upperEndpoint y (fun _ => 1) α β = binaryUpper (populationMean y) (β/α) ∧
    (populationMean y = 0 → binaryLower (populationMean y) (β/α) = 0 ∧
      binaryUpper (populationMean y) (β/α) = 0) ∧
    (populationMean y = 1 → binaryLower (populationMean y) (β/α) = 1 ∧
      binaryUpper (populationMean y) (β/α) = 1) ∧
    (β/α = 1 → binaryLower (populationMean y) (β/α) = populationMean y ∧
      binaryUpper (populationMean y) (β/α) = populationMean y)

/-- Printed Proposition 3, retaining separation only on the valid finite cut range. -/
def T21Statement : Prop :=
  ∀ {N J : ℕ}, 0 < N → 0 < J →
    ∀ {κ : Type*} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
      (d : FiniteDesign (Fin N) κ) (cls : Fin N → Fin J),
      Function.Surjective cls → ∀ (y : Fin J → ℝ), StrictMono y →
      ∀ (α β : ℝ), 0 < α → α ≤ β → β ≤ 1 →
      (∀ i, α ≤ inclusion d i ∧ inclusion d i ≤ β) →
      separation y (classTotal d cls) (β/α) → PooledConvergence d cls y α β


end
end SAP.P025b
