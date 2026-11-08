import Mathlib
import SAP.P025b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b
noncomputable section
open scoped BigOperators

/-- The first `k` observations, with observations indexed from zero and a
cut indexed by its prefix length. An empty prefix has sum zero. -/
def t19Prefix {n : ℕ} (y : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i with i.val < k, y i

/-- Observations after a prefix of length `k`. An empty tail has sum zero. -/
def t19Tail {n : ℕ} (y : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i with k ≤ i.val, y i

/-- The upper denominator in Supplement step (iii). The whole statement
uses it only for `k ≤ n`, and asserts its positivity there. -/
def t19UpperDen (n : ℕ) (γ : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) + γ * ((n : ℝ) - (k : ℝ))

/-- The corrected lower denominator in Supplement step (iv). Subtraction
is in the reals; its arguments in the whole statement satisfy `k ≤ n`. -/
def t19LowerDen (n : ℕ) (γ : ℝ) (k : ℕ) : ℝ :=
  γ * (k : ℝ) + ((n : ℝ) - (k : ℝ))

/-- P025-T19; p. 237 (PDF p. 3); proof in the Supplement, p. 1.
For a sorted sample of at least two outcomes and 0 < alpha <= beta <= 1,
the upper and corrected lower least cuts exist uniquely and select feasible
optimal physical weights. Every tied pair receives equal weights. When
gamma = beta/alpha > 1, equality of adjacent weights is equivalent to the
cut not separating that pair, so neither cut separates tied observations.
All finite threshold formulas have positive denominators. For constant
outcomes the upper cut is zero and every upper weight is 1/alpha;
otherwise the zero-cut upper value is the sample mean, strictly above the
first outcome, and the upper cut is positive. At each adjacent tie at or
before either cut, the preceding test fails strictly, the corresponding
Supplement numerator/residual recurrence propagates strict failure, and
the next cut index is still at or before the selected cut.
-/
def T19WholeStatement : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n) (y : Fin n → ℝ), Monotone y →
    ∀ (α β : ℝ), 0 < α → α ≤ β → β ≤ 1 →
    let γ := β / α
    let FH := upperValue y (fun _ => 1) γ
    let FL := lowerValue y (fun _ => 1) γ
    let first : Fin n := ⟨0, by omega⟩
    (∀ k : ℕ, k ≤ n →
      0 < t19UpperDen n γ k ∧ 0 < t19LowerDen n γ k ∧
      FH k = (t19Prefix y k + γ * t19Tail y k) / t19UpperDen n γ k ∧
      FL k = (γ * t19Prefix y k + t19Tail y k) / t19LowerDen n γ k) ∧
    ∃ kL kH : Fin n,
      let wL := fun i : Fin n => (1 / β) * lowerWeights γ kL.val i
      let wH := fun i : Fin n => (1 / β) * upperWeights γ kH.val i
      lowerCut y (fun _ => 1) γ kL ∧ upperCut y (fun _ => 1) γ kH ∧
      (∀ jL jH : Fin n,
        lowerCut y (fun _ => 1) γ jL → upperCut y (fun _ => 1) γ jH →
        jL = kL ∧ jH = kH) ∧
      (∀ i : Fin n,
        wL i = (if i.val < kL.val then 1 / α else 1 / β) ∧
        wH i = (if i.val < kH.val then 1 / β else 1 / α)) ∧
      weightBox α β wL ∧ weightBox α β wH ∧
      IsLeast (attainable y (fun _ => 1) α β) (ratio y (fun _ => 1) wL) ∧
      IsGreatest (attainable y (fun _ => 1) α β) (ratio y (fun _ => 1) wH) ∧
      (∀ i j : Fin n, y i = y j → wL i = wL j ∧ wH i = wH j) ∧
      (1 < γ → ∀ i j : Fin n, j.val = i.val + 1 →
        (wL i = wL j ↔ kL.val ≠ j.val) ∧
        (wH i = wH j ↔ kH.val ≠ j.val) ∧
        (y i = y j → kL.val ≠ j.val ∧ kH.val ≠ j.val)) ∧
      (∀ c : ℝ, (∀ i, y i = c) →
        kH.val = 0 ∧ ∀ i, wH i = 1 / α) ∧
      ((¬ ∀ i, y i = y first) →
        FH 0 = populationMean y ∧ y first < FH 0 ∧ 0 < kH.val) ∧
      (∀ i j : Fin n, j.val = i.val + 1 → j.val ≤ kH.val → y i = y j →
        y i < FH i.val ∧
        FH j.val =
          ((1 - γ) * y i + t19Prefix y i.val + γ * t19Tail y i.val) /
            t19UpperDen n γ j.val ∧
        ((1 - γ) * y i + t19UpperDen n γ i.val * y i) /
            t19UpperDen n γ j.val = y i ∧
        ((1 - γ) * y i + t19UpperDen n γ i.val * y i) /
            t19UpperDen n γ j.val < FH j.val ∧
        FH j.val - y i =
          (t19UpperDen n γ i.val / t19UpperDen n γ j.val) *
            (FH i.val - y i) ∧
        0 < FH j.val - y i ∧ y j < FH j.val ∧ j.val + 1 ≤ kH.val) ∧
      (∀ i j : Fin n, j.val = i.val + 1 → j.val ≤ kL.val → y i = y j →
        y i < FL i.val ∧
        FL j.val - y i =
          (t19LowerDen n γ i.val * (FL i.val - y i)) /
            t19LowerDen n γ j.val ∧
        0 < FL j.val - y i ∧ y j < FL j.val ∧ j.val + 1 ≤ kL.val)

end
end SAP.P025b
