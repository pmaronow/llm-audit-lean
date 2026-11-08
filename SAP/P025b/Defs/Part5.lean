import Mathlib
import SAP.P025b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

/-- Shares-only sharpness, rational attainment, and retained-total calibration.
The assertion that the outer bound can fail to be sharp with richer information
is intentionally absent. -/
def T15Statement : Prop :=
  ∀ {J : ℕ}, 0 < J → ∀ (y q : Fin J → ℝ), StrictMono y →
    (∀ j, 0 < q j) → (∑ j, q j) = 1 →
    ∀ (α β : ℝ), 0 < α → α ≤ β → β ≤ 1 →
    (∃ m : Fin J → ℕ, sharesCompatible α β q m) →
    (∀ (m : Fin J → ℕ) (mass : Fin J → ℝ),
      (∀ j, 0 < mass j) → absoluteCompatible α β mass m →
      weightBox α β (fun j => (m j : ℝ)/mass j) ∧
      ratio y mass (fun j => (m j : ℝ)/mass j) = classMean y m) ∧
    (∀ m : Fin J → ℕ, sharesCompatible α β q m →
      lowerEndpoint y q α β ≤ classMean y m ∧
      classMean y m ≤ upperEndpoint y q α β) ∧
    IsGLB (compatibleMeans y q α β) (lowerEndpoint y q α β) ∧
    IsLUB (compatibleMeans y q α β) (upperEndpoint y q α β) ∧
    {r | ∃ W, weightBox α β W ∧ weightProportions q W = r} =
      {r | proportionRegion q (β/α) r} ∧
    IsLeast {v | ∃ r : Fin J → ℝ, proportionRegion q (β/α) r ∧ (∑ j, r j*y j) = v}
      (lowerEndpoint y q α β) ∧
    IsGreatest {v | ∃ r : Fin J → ℝ, proportionRegion q (β/α) r ∧ (∑ j, r j*y j) = v}
      (upperEndpoint y q α β) ∧
    (∀ r : Fin J → ℝ, (∃ m : Fin J → ℕ,
      sharesCompatible α β q m ∧ classProportions m = r) ↔
      proportionRegion q (β/α) r ∧ rationalVector r) ∧
    ((lowerEndpoint y q α β ∈ compatibleMeans y q α β) ↔
      ∃ r : Fin J → ℝ, proportionRegion q (β/α) r ∧ rationalVector r ∧
        (∑ j, r j*y j) = lowerEndpoint y q α β) ∧
    ((upperEndpoint y q α β ∈ compatibleMeans y q α β) ↔
      ∃ r : Fin J → ℝ, proportionRegion q (β/α) r ∧ rationalVector r ∧
        (∑ j, r j*y j) = upperEndpoint y q α β) ∧
    (∀ (mass : Fin J → ℝ) (m : Fin J → ℕ),
      absoluteCompatible α β mass m ↔
        ∀ j, 0 < m j ∧ mass j/β ≤ (m j : ℝ) ∧ (m j : ℝ) ≤ mass j/α) ∧
    (∀ (mass : Fin J → ℝ), (∀ j, 0 < mass j) →
      ∀ m : Fin J → ℕ, absoluteCompatible α β mass m →
      lowerEndpoint y mass α β ≤ classMean y m ∧
      classMean y m ≤ upperEndpoint y mass α β) ∧
    (∀ (mass : Fin J → ℝ) (N : ℕ) (v : ℝ),
      v ∈ knownSizeCompatibleMeans y mass α β N ↔
        ∃ m : Fin J → ℕ,
          (∀ j, 0 < m j ∧ mass j/β ≤ (m j : ℝ) ∧ (m j : ℝ) ≤ mass j/α) ∧
          (∑ j, m j) = N ∧ classMean y m = v) ∧
    (∀ (mass : Fin J → ℝ) (m : Fin J → ℕ),
      absoluteCompatible α β mass m ↔
        (∀ j, 0 < m j) ∧ ∀ j, ∃ π : Fin (m j) → ℝ,
          (∀ i, α ≤ π i ∧ π i ≤ β) ∧ ∑ i, π i = mass j)


end
end SAP.P025b
