import SAP.P007.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P007
open scoped BigOperators

/-- An actual normalized independent-cell model with the displayed weights. -/
def equalModel (n h : ℕ) (q : ℝ) (P : Law (Array n h) → Prop) : Prop :=
  ∃ L : Law (Array n h), L.weight = equalWeights n h q ∧
    rowIndependent L ∧ observationBound L q ∧ P L

def unequalModel (n h : ℕ) (P : Law (Array n h) → Prop) : Prop :=
  ∃ L : Law (Array n h), L.weight = unequalWeights n h ∧
    rowIndependent L ∧ observationBound L (3/4) ∧ P L

def workedValues : Prop :=
  ⌊realThreshold 10000 (3/4) (1/2)⌋₊ = 33 ∧
  ⌈realThreshold 10000 (3/4) (1/2)⌉₊ = 34 ∧
  ⌊realThreshold 10000 (99/100) (1/2)⌋₊ = 952 ∧
  ⌈realThreshold 10000 (99/100) (1/2)⌉₊ = 953 ∧
  (0.47075 : ℝ) ≤ lowerBound 10000 (3/4) 33 ∧
  lowerBound 10000 (3/4) 33 < 0.47085 ∧
  (0.49685 : ℝ) ≤ lowerBound 10000 (99/100) 952 ∧
  lowerBound 10000 (99/100) 952 < 0.49695

def T7Statement : Prop :=
  equalModel 1 2 (3/4) (fun L =>
    lowerBound 1 (3/4) 2 = 7/16 ∧ lowerBound 1 (3/4) 3 = 37/64 ∧
    lowerBound 1 (3/4) 2 < 1/2 ∧ (1/2 : ℝ) < lowerBound 1 (3/4) 3 ∧
    (2 : ℝ) < realThreshold 1 (3/4) (1/2) ∧ realThreshold 1 (3/4) (1/2) < 3 ∧
    ⌊realThreshold 1 (3/4) (1/2)⌋₊ = 2 ∧ ⌈realThreshold 1 (3/4) (1/2)⌉₊ = 3 ∧
    (∀ k : ℕ, lowerBound 1 (3/4) k ≠ 1/2) ∧ allDeleted L = 7/16 ∧
    (∀ k : ℕ, lowerBound 1 (3/4) k ≤ 1/2 ↔ k ≤ 2) ∧
    (∀ k : ℕ, (1/2 : ℝ) ≤ lowerBound 1 (3/4) k ↔ 3 ≤ k) ∧
    realLowerBound 1 (3/4) (realThreshold 1 (3/4) (1/2)) = 1/2) ∧
  equalModel 10000 33 (3/4) (fun L =>
    allDeleted L = lowerBound 10000 (3/4) 33 ∧ allDeleted L < 1/2 ∧
    (1/2 : ℝ) < lowerBound 10000 (3/4) 34) ∧
  equalModel 10000 952 (99/100) (fun L =>
    allDeleted L = lowerBound 10000 (99/100) 952 ∧ allDeleted L < 1/2 ∧
    (1/2 : ℝ) < lowerBound 10000 (99/100) 953) ∧
  unequalModel 1 2 (fun L =>
    lowerBound 1 (3/4) 2 = 7/16 ∧ lowerBound 1 (3/4) 2 ≤ 1/2 ∧
    allDeleted L = 13/16 ∧ (1/2 : ℝ) < allDeleted L) ∧
  unequalModel 1 16 (fun L =>
    lowerBound 1 (3/4) 16 = 4251920575/4294967296 ∧
    lowerBound 1 (3/4) 16 < 99/100 ∧ (99/100 : ℝ) < lowerBound 1 (3/4) 17 ∧
    allDeleted L = 4294967293/4294967296 ∧ (99/100 : ℝ) < allDeleted L ∧
    ⌊realThreshold 1 (3/4) (99/100)⌋₊ = 16 ∧
    ⌈realThreshold 1 (3/4) (99/100)⌉₊ = 17) ∧
  unequalModel 10000 33 (fun L =>
    allDeleted L = (1 - (3 : ℝ)/4^33)^10000 ∧
    1 - (30000 : ℝ)/4^33 ≤ allDeleted L ∧
    (99/100 : ℝ) < 1 - (30000 : ℝ)/4^33 ∧
    (99/100 : ℝ) < allDeleted L ∧ lowerBound 10000 (3/4) 33 < 1/2) ∧
  (⌊realThreshold 10000 (3/4) (1/2)⌋₊ = 33 ∧
    ⌈realThreshold 10000 (3/4) (1/2)⌉₊ = 34 ∧
    ⌊realThreshold 10000 (99/100) (1/2)⌋₊ = 952 ∧
    ⌈realThreshold 10000 (99/100) (1/2)⌉₊ = 953)

def T8Statement : Prop :=
  (∀ n : ℕ, 0 < n → ∀ q a : ℝ, 0 < q → q < 1 → 0 < a → a < 1 →
    (lowerBound n q 0 = 0 ∧ (∀ k, 0 ≤ lowerBound n q k ∧ lowerBound n q k < 1) ∧
      StrictMono (lowerBound n q)) ∧
    (0 < realThreshold n q a ∧ realLowerBound n q (realThreshold n q a) = a ∧
      ∀ x : ℝ, 0 ≤ x → realLowerBound n q x = a → x = realThreshold n q a) ∧
    (∀ k : ℕ, (lowerBound n q k ≤ a ↔ (k : ℝ) ≤ realThreshold n q a) ∧
      (a ≤ lowerBound n q k ↔ realThreshold n q a ≤ (k : ℝ)) ∧
      (lowerBound n q k = a ↔ (k : ℝ) = realThreshold n q a)) ∧
    ((∀ k : ℕ, lowerBound n q k ≤ a ↔ k ≤ ⌊realThreshold n q a⌋₊) ∧
      (∀ k : ℕ, a ≤ lowerBound n q k ↔ ⌈realThreshold n q a⌉₊ ≤ k) ∧
      lowerBound n q ⌊realThreshold n q a⌋₊ ≤ a ∧
      a ≤ lowerBound n q ⌈realThreshold n q a⌉₊) ∧
    ((⌈realThreshold n q a⌉₊ = ⌊realThreshold n q a⌋₊ ↔
        ∃ m : ℕ, (m : ℝ) = realThreshold n q a) ∧
      ((¬ ∃ m : ℕ, (m : ℝ) = realThreshold n q a) →
        ⌈realThreshold n q a⌉₊ = ⌊realThreshold n q a⌋₊ + 1 ∧
        lowerBound n q ⌊realThreshold n q a⌋₊ < a ∧
        a < lowerBound n q ⌈realThreshold n q a⌉₊)) ∧
    (∀ k : ℕ, 0 < k → ∀ L : Law (Array n k),
      rowIndependent L → observationBound L q →
      lowerBound n q k ≤ allDeleted L ∧
        (⌈realThreshold n q a⌉₊ ≤ k → a ≤ lowerBound n q k ∧ a ≤ allDeleted L)) ∧
    (∀ k : ℕ, 0 < k → (k : ℝ) < realThreshold n q a →
      equalModel n k q (fun L => allDeleted L = lowerBound n q k ∧ allDeleted L < a)) ∧
    (∀ k : ℕ, 0 < k → equalModel n k q (fun L => allDeleted L = lowerBound n q k))) ∧
  workedValues ∧
  (lowerBound 10000 (3/4) 33 < 1/2 ∧ (1/2 : ℝ) < lowerBound 10000 (3/4) 34 ∧
    lowerBound 10000 (99/100) 952 < 1/2 ∧ (1/2 : ℝ) < lowerBound 10000 (99/100) 953) ∧
  unequalModel 1 2 (fun L => lowerBound 1 (3/4) 2 ≤ 1/2 ∧ (1/2 : ℝ) < allDeleted L)

def T9Statement : Prop :=
  ∃ L : Law (Array 2 2), L.weight = figure5Weights ∧
    rowIndependent L ∧ observationBound L (3/4) ∧
    (∀ q : ℝ, observationBound L q → (3/4 : ℝ) ≤ q) ∧
    (∀ i, survival L i 1 = 3/4 ∧ survival L i 2 = 3/8 ∧
      0 < survival L i 1 ∧ survival L i 2 / survival L i 1 = 1/2) ∧
    (∀ i, expectation L (fun x => deletedIndicator x i) = 5/8) ∧
    expectation L deletedFraction = 5/8 ∧ fractionBound (3/4) 2 = 7/16 ∧
    fractionBound (3/4) 2 < expectation L deletedFraction ∧
    lowerBound 2 (3/4) 2 = 49/256 ∧ lowerBound 2 (3/4) 2 ≠ fractionBound (3/4) 2 ∧
    allDeleted L = 25/64

def T10Statement : Prop :=
  (∀ (n k : ℕ), 0 < n → 0 < k → ∀ (L : Law (Array n k)) (q : ℝ),
    observationBound L q →
    (∀ i, expectation L (fun x => deletedIndicator x i) = 1 - survival L i k ∧
      fractionBound q k ≤ expectation L (fun x => deletedIndicator x i)) ∧
    (expectation L deletedFraction = (∑ i, (1 - survival L i k)) / n ∧
      fractionBound q k ≤ expectation L deletedFraction)) ∧
  (∀ (n k : ℕ), 0 < n → 0 < k → ∀ q : ℝ, 0 ≤ q → q < 1 →
    equalModel n k q (fun L => expectation L deletedFraction = fractionBound q k)) ∧
  (∀ (n k : ℕ), 0 < n → 0 < k → ∀ q : ℝ, 0 ≤ q → q < 1 →
    lowerBound n q k = (fractionBound q k)^n ∧
    lowerBound 1 q k = fractionBound q k) ∧
  (∀ (n k : ℕ), 2 ≤ n → 0 < k → ∀ q : ℝ, 0 < q → q < 1 →
    0 < fractionBound q k ∧ fractionBound q k < 1 ∧ lowerBound n q k < fractionBound q k) ∧
  (∀ (n k : ℕ), 0 < n → 0 < k → ∀ q : ℝ, 0 < q → q < 1 →
    (lowerBound n q k = fractionBound q k ↔ n = 1)) ∧
  (∀ (n k : ℕ), 0 < n → 0 < k → fractionBound 0 k = 1 ∧ lowerBound n 0 k = 1)

def T11Statement : Prop :=
  (∀ (n k : ℕ), 0 < n → 0 < k → ∀ L : Law (Array n k), rowIndependent L →
    allDeleted L = ∏ i, (1 - survival L i k)) ∧
  (∃ L : Law (Array 2 1), L.weight = nonidenticalWeights ∧
    rowIndependent L ∧ observationBound L (1/2) ∧ ¬ sameRowLaw L ∧
    survival L 0 1 = 1/4 ∧ survival L 1 1 = 1/2 ∧
    allDeleted L = 3/8 ∧ lowerBound 2 (1/2) 1 = 1/4 ∧
    lowerBound 2 (1/2) 1 ≤ allDeleted L)

end SAP.P007
