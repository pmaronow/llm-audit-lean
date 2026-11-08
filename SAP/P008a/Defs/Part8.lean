import Mathlib
import SAP.P008a.Defs.Part1
import SAP.P008a.Defs.Part2
import SAP.P008a.Defs.Part3
import SAP.P008a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P008a

open MeasureTheory Filter
open scoped BigOperators Classical

noncomputable section

/-- The mathematical statement of P008-T10. -/
def T10Statement : Prop :=
  (∀ {N : ℕ} (z : Assignment N) (M : Fin N → ℝ) (D : Fin N → Fin N → ℝ)
    (c : ℝ) (h₁ : nTreated z ≠ 0) (h₀ : nControl z ≠ 0) (j k : ℕ),
    physicalVariance (regressionScore z M) D c j = hac (regressionScore z M) D c ∧
    physicalVariance (regressionScore z M) D c j = physicalVariance (regressionScore z M) D c k ∧
    (∑ i, regressionScore z M i) = 0 ∧
    (∀ (hall : ∀ i l, D i l ≤ c),
      hac (regressionScore z M) D c = (∑ i, regressionScore z M i)^2 ∧
      hac (regressionScore z M) D c = 0)) ∧
  (physicalVariance ![1 / 2, -1 / 2, -1 / 2, 1 / 2] bandwidthExampleDistance (2 / 5) 1 = 1 ∧
  physicalVariance ![1 / 2, -1 / 2, -1 / 2, 1 / 2] bandwidthExampleDistance (2 / 5) 2 = 1) ∧
  (∀ (z : Assignment 4) (M : Fin 4 → ℝ)
    (h₁ : nTreated z ≠ 0) (h₀ : nControl z ≠ 0),
    hac (regressionScore z M) (fun i j => dist (toyNode i) (toyNode j)) (2 / 5) =
      ∑ i, (regressionScore z M i)^2 ∧
    hac (regressionScore z M) (fun i j => dist (toyNode i) (toyNode j)) (2 / 5) =
      hac (regressionScore z M) (fun i j => dist (toyNode i) (toyNode j)) 0 ∧
    archivedVariance (regressionScore z M)
      (fun i j => dist (toyNode i) (toyNode j)) (2 / 5) 6 = 0)

/-- The mathematical statement of P008-T11. -/
def T11Statement : Prop :=
  ((1491 / 1000 : ℝ) + 1550 / 1000 + 1550 / 1000 + 1691 / 1000 + 1714 / 1000 =
      1999 / 250 ∧
    (1999 / 250 : ℝ) + 1700 / 1000 + 1678 / 1000 + 1002 / 1000 = 1547 / 125) ∧
  (∀ (a b c e f : ℝ)
    (ha : |a - 1491 / 1000| ≤ 1 / 2000)
    (hb : |b - 1550 / 1000| ≤ 1 / 2000)
    (hc : |c - 1550 / 1000| ≤ 1 / 2000)
    (he : |e - 1691 / 1000| ≤ 1 / 2000)
    (hf : |f - 1714 / 1000| ≤ 1 / 2000),
    15987 / 2000 ≤ a + b + c + e + f ∧
    a + b + c + e + f ≤ 15997 / 2000 ∧
    1 / 200 < |(a + b + c + e + f) - 619 / 50| ∧
    1595 / 200 < a + b + c + e + f) ∧
  (|(1547 / 125 : ℝ) - 619 / 50| < 1 / 200)

/-- The mathematical statement of P008-T12. -/
def T12Statement : Prop :=
  ((∀ k : Fin 5, ¬ inUgandaRange (printedGrid k)) ∧
    (∀ f : Fin 5 → ℝ, ∑ k ∈ Finset.univ.filter
      (fun k => inUgandaRange (printedGrid k)), f k = 0) ∧
    (-321 / 10000 : ℝ) ≠ 0 ∧ (-19 / 625 : ℝ) ≠ 0 ∧ (21 / 625 : ℝ) ≠ 0) ∧
  ((25 / 111 : ℝ) > 20 / 111) ∧
  (∀ {n : ℕ} (M : Fin (n + 1) → Fin 5 → ℝ) (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1),
    (∀ z, ∑ j ∈ Finset.univ.filter (fun j => inUgandaRange (printedGrid j)), M z j = 0) ∧
    quantile7 (fun z => ∑ j ∈ Finset.univ.filter
      (fun j => inUgandaRange (printedGrid j)), M z j) q = 0)

/-- The mathematical statement of P008-T13. -/
def T13Statement : Prop :=
  (Fintype.card (Fin 41) = 41 ∧ correctedGrid 40 = 20 / 111 ∧
    (∀ k : Fin 41, inUgandaRange (correctedGrid k) ↔ 2 ≤ k.val ∧ k.val ≤ 5) ∧
    (∀ f : Fin 41 → ℝ, ∑ k ∈ Finset.univ.filter
      (fun k => inUgandaRange (correctedGrid k)), f k = f 2 + f 3 + f 4 + f 5) ∧
    (∀ k : Fin 40, correctedGrid k.succ - correctedGrid k.castSucc = 1 / 222)) ∧
  ((111 * correctedGrid 2 = (1 : ℝ)) ∧ (111 * correctedGrid 3 = (3 / 2 : ℝ)) ∧
  (111 * correctedGrid 4 = (2 : ℝ)) ∧ (111 * correctedGrid 5 = (5 / 2 : ℝ)) ∧
  (1 / 222 : ℝ) = (1 / 2) / 111)

/-- The mathematical statement of P008-T14. -/
def T14Statement : Prop :=
  (∀ {N : ℕ} (hN : 0 < N) (μ₁ μ₀ τ : Fin N → ℝ)
    (hτ : ∀ i, τ i = μ₁ i - μ₀ i),
    (N : ℝ)⁻¹ * ∑ i, τ i = (N : ℝ)⁻¹ * ∑ i, (μ₁ i - μ₀ i)) ∧
  (∀ (A : ℝ),
    A * A = A ↔ A = 0 ∨ A = 1) ∧
  (((3 - 0 + (7 - 2)) / 2 : ℝ) = 4 ∧ (4 : ℝ) * 4 = 16 ∧ (16 : ℝ) ≠ 4)

end
end SAP.P008a
