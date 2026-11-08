import SAP.P007.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P007
open Filter Topology
open scoped BigOperators

def T12Statement : Prop :=
  (∀ (n K d : ℕ), 0 < n → 0 < K → ∀ m : Fin n → (Fin K ⊕ Fin d) → Bool,
    (∀ i j, m i (Sum.inr j) = true) →
    let A := missingCount m
    let after := fun i j => m i (Sum.inl j)
    A = missingCount after + n*d ∧
    missingAverage m = (A : ℝ) / ((n : ℝ) * (K + d)) ∧
    missingAverage after = ((A : ℝ) - n*d) / ((n : ℝ) * K) ∧
    ((K + d : ℕ) : ℝ) * missingAverage m = (d : ℝ) + K * missingAverage after ∧
    missingAverage after = (((K + d : ℕ) : ℝ) * missingAverage m - d) / K) ∧
  (∀ m : Fin 8580 → (Fin 1205 ⊕ Fin 19) → Bool,
    (∀ i j, m i (Sum.inr j) = true) →
    (0.6675 : ℝ) ≤ missingAverage m → missingAverage m < 0.6685 →
    missingAverage (fun i j => m i (Sum.inl j)) < (199811 : ℝ)/301250 ∧
    (199811 : ℝ)/301250 < 0.6675 ∧
    missingAverage (fun i j => m i (Sum.inl j)) < 0.6675) ∧
  (∀ m : Fin 8580 → (Fin 1205 ⊕ Fin 19) → Bool,
    (∀ i j, m i (Sum.inr j) = true) → missingCount m = 7019387 →
    missingAverage m = (7019387 : ℝ)/10501920 ∧
    missingAverage (fun i j => m i (Sum.inl j)) = (6856367 : ℝ)/10338900 ∧
    (0.6625 : ℝ) ≤ missingAverage (fun i j => m i (Sum.inl j)) ∧
    missingAverage (fun i j => m i (Sum.inl j)) < 0.6635 ∧
    missingAverage m - missingAverage (fun i j => m i (Sum.inl j)) =
      (66168127 : ℝ)/12654813600 ∧
    100 * (missingAverage m - missingAverage (fun i j => m i (Sum.inl j))) =
      (66168127 : ℝ)/126548136)

def T14Statement : Prop :=
  ∀ (n k : ℕ), 0 < n → 0 < k → ∀ (L : Law (Array n k)) (q : ℝ),
    rowIndependent L → observationBound L q → (1 - q^k)^n ≤ allDeleted L

def T15Statement : Prop :=
  ∀ (n g : ℕ), 0 < n → 0 < g → ∀ (L : Law (Array n g)) (q : ℝ),
    rowIndependent L → observationBound L q → (1 - q^g)^n ≤ allDeleted L

/-- The sequence is extended to n=0 solely to use the full natural-number filter;
the probability assumptions and positive dimension requirement start at n=1. -/
def T16Statement : Prop :=
  ∀ (k : ℕ → ℕ) (L : ∀ n, Law (Array n (k n))),
    (∀ n, 0 < n → 0 < k n) → ∀ q : ℝ, 0 ≤ q → q < 1 →
    (∀ n, 0 < n → rowIndependent (L n)) →
    (∀ n, 0 < n → observationBound (L n) q) → superlog k →
    Tendsto (fun n => allDeleted (L n)) atTop (𝓝 1)

def T17Statement : Prop :=
  ∀ (g : ℕ → ℕ) (L : ∀ n, Law (Array n (g n))),
    (∀ n, 0 < n → 0 < g n) → ∀ q : ℝ, 0 ≤ q → q < 1 →
    (∀ n, 0 < n → rowIndependent (L n)) →
    (∀ n, 0 < n → observationBound (L n) q) → superlog g →
    Tendsto (fun n => allDeleted (L n)) atTop (𝓝 1)

end SAP.P007
