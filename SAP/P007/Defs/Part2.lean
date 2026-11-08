import SAP.P007.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P007
open scoped BigOperators

/-- The complete four-variable certificate, including the counting identity and
all arithmetic clauses of the canonical exact refutation. -/
def T1Statement : Prop :=
  (∀ m : ObservedArray 8580 1205,
    meanRetained m 4 = (∑ i, ((m i).card.choose 4 : ℝ)) /
      ((8580 : ℝ) * (Nat.choose 1205 4 : ℝ)) ∧
    ((∑ i, ((m i).card : ℤ)) = 3482533 →
      (9560288484630 : ℤ) ≤ ∑ i, ((m i).card.choose 4 : ℤ) ∧
      (24513560217 : ℝ)/1923069889510 ≤ meanRetained m 4 ∧
      (1 : ℝ)/100 < meanRetained m 4 ∧
      meanLoss m 4 ≤ (1898556329293 : ℝ)/1923069889510 ∧
      meanLoss m 4 < (99 : ℝ)/100)) ∧
  (∀ r : Fin 1206, (1104475905 : ℤ) + ((r.val : ℤ) - 405) * 10989810 ≤
    (r.val.choose 4 : ℤ)) ∧
  ((Nat.choose 405 4 : ℤ) = 1104475905 ∧ (Nat.choose 405 3 : ℤ) = 10989810 ∧
    (Nat.choose 406 4 : ℤ) = 1115465715) ∧
  (8580 : ℤ) * (Nat.choose 1205 4 : ℤ) = 749997256908900 ∧
  (947 : ℤ) * Nat.choose 405 4 + 7633 * Nat.choose 406 4 = 9560288484630 ∧
  (3482533 : ℤ) = 8580 * 405 + 7633 ∧
  (9560288484630 : ℝ)/749997256908900 = 24513560217/1923069889510 ∧
  (1 : ℝ)/100 < 24513560217/1923069889510 ∧
  (1898556329293 : ℝ)/1923069889510 < 99/100 ∧
  (Nat.choose 405 4 : ℤ) = 1104475905 + ((405 : ℤ) - 405) * 10989810 ∧
  (Nat.choose 406 4 : ℤ) = 1104475905 + ((406 : ℤ) - 405) * 10989810 ∧
  (1 : ℝ) - 24513560217/1923069889510 = 1898556329293/1923069889510

def averageArithmetic : Prop :=
  8580 * 1224 = (10501920 : ℕ) ∧ 8580 * 19 = (163020 : ℕ) ∧
  7019387 - 8580 * 19 = (6856367 : ℕ) ∧ 8580 * 1205 = (10338900 : ℕ) ∧
  10338900 - 6856367 = (3482533 : ℕ) ∧
  (0.6625 : ℝ) ≤ 6856367/10338900 ∧ (6856367 : ℝ)/10338900 < 0.6635 ∧
  (6856367 : ℝ)/10338900 < 0.6675 ∧
  (0.6675 : ℝ) ≤ 7019387/10501920 ∧ (7019387 : ℝ)/10501920 < 0.6685

def simulationComparisons : Prop :=
  (1 - 0.02820753 : ℝ) = 0.97179247 ∧
  (1 - 0.01365003 : ℝ) = 0.98634997 ∧
  (1 - 0.006640252 : ℝ) = 0.993359748 ∧
  (0.97179247 : ℝ) < 0.98634997 ∧
  (0.98634997 : ℝ) < 0.99 ∧ (0.99 : ℝ) < 0.993359748

def correctedMask (m : Fin 8580 → (Fin 1205 ⊕ Fin 19) → Bool) : Prop :=
  let after := fun i j => m i (Sum.inl j)
  missingCount m = 7019387 ∧ missingCount after = 6856367 ∧
  (∑ i, (observedColumns after i).card) = 3482533 ∧
  missingAverage m = (7019387 : ℝ)/10501920 ∧
  missingAverage after = (6856367 : ℝ)/10338900 ∧
  (0.6625 : ℝ) ≤ missingAverage after ∧ missingAverage after < 0.6635 ∧
  missingAverage after < 0.6675 ∧
  meanLoss (observedColumns after) 4 ≤ (1898556329293 : ℝ)/1923069889510 ∧
  meanLoss (observedColumns after) 4 < (99 : ℝ)/100

def T2Statement : Prop :=
  (∀ A : ℕ, |(A : ℝ)/10501920 - (0.668390827582004 : ℝ)| ≤ 0.000000001 →
    A = 7019387) ∧ averageArithmetic ∧
  (∀ m : Fin 8580 → (Fin 1205 ⊕ Fin 19) → Bool,
    (∀ i j, m i (Sum.inr j) = true) →
    |missingAverage m - (0.668390827582004 : ℝ)| ≤ 0.000000001 → correctedMask m) ∧
  (∀ m : ObservedArray 8580 1205, (∑ i, ((m i).card : ℤ)) = 3482533 →
    meanLoss m 4 ≤ (1898556329293 : ℝ)/1923069889510 ∧ meanLoss m 4 < (99 : ℝ)/100) ∧
  simulationComparisons

def T3Statement : Prop :=
  (∃ L : Law (Array 1 2), L.weight = nullFirstWeights ∧
    rowIndependent L ∧ observationBound L 0 ∧ survival L 0 1 = 0 ∧
    survival L 0 2 = 0 ∧ probability L (fun x => x 0 1 = false) = 1 ∧
    probability L (fun x => x 0 1 = true) = 0 ∧
    allDeleted L = 1 ∧ (1 - (0 : ℝ)^2)^1 = 1) ∧
  (∃ L : Law (Array 1 2), L.weight = fullyMissingWeights ∧
    ∀ q : ℝ, 0 ≤ q → q < 1 → rowIndependent L ∧ observationBound L q ∧
      ∀ j : Fin 2, probability L (fun x => x 0 j = true) = 1)

def T4Statement : Prop :=
  (∃ L : Law (Array 1 2), L.weight = nullFirstWeights ∧
    rowIndependent L ∧ observationBound L (1/2) ∧
    survival L 0 1 = 0 ∧ survival L 0 2 = 0 ∧
    (∀ v : ℝ, 0 ≤ v → v ≤ 1 → survival L 0 2 = v * survival L 0 1) ∧
    (1/2 : ℝ) < 1 ∧ survival L 0 2 ≤ (1/2 : ℝ)^2 ∧
    allDeleted L = 1 ∧ (3/4 : ℝ) ≤ allDeleted L) ∧
  (∃ L : Law (Array 2 3), L.weight = laterNullWeights ∧
    rowIndependent L ∧ observationBound L (1/2) ∧
    (∀ i, survival L i 1 = 1/2 ∧ survival L i 2 = 0 ∧ survival L i 3 = 0 ∧
      0 < survival L i 1 ∧ survival L i 2 / survival L i 1 = 0 ∧
      survival L i 3 ≤ (1/8 : ℝ)) ∧
    allDeleted L = 1 ∧ (49/64 : ℝ) ≤ allDeleted L)

def T5Statement : Prop :=
  ∀ (n h : ℕ), 0 < n → ∀ hh : 0 < h, ∀ (L : Law (Array n h)) (q : ℝ),
    observationBound L q →
    (q = 0 → (∀ i, probability L (fun x => x i ⟨0, hh⟩ = true) = 1) ∧
      allDeleted L = 1 ∧ (1 - q^h)^n = 1) ∧
    (∀ i, survival L i 0 = 1) ∧
    (∀ i j, j < h → survival L i (j + 1) ≤ survival L i j * q) ∧
    (∀ i j, j < h → survival L i j = 0 → survival L i (j + 1) = 0) ∧
    (∀ i, conditionalObserved L i 0 = survival L i 1 ∧
      survival L i h = ∏ t ∈ Finset.range h, conditionalObserved L i t ∧
      (∀ j, j < h → 0 ≤ conditionalObserved L i j ∧ conditionalObserved L i j ≤ q) ∧
      survival L i h ≤ q^h ∧ 1 - q^h ≤ 1 - survival L i h) ∧
    (rowIndependent L → allDeleted L = ∏ i, (1 - survival L i h) ∧
      (1 - q^h)^n ≤ allDeleted L)

def T6Statement : Prop :=
  (∀ (n h : ℕ), 0 < n → 0 < h → ∀ q : ℝ, 0 ≤ q → q < 1 →
    -1 < -(q^h) ∧ 1 - q^h ≤ 1 ∧
    1 + (n : ℝ) * (-(q^h)) = 1 - (n : ℝ) * q^h ∧
    1 - (n : ℝ) * q^h ≤ (1 - q^h)^n ∧ (1 - q^h)^n ≤ 1) ∧
  (∀ (n h : ℕ), 0 < n → 0 < h → ∀ (L : Law (Array n h)) (q : ℝ),
    rowIndependent L → observationBound L q →
    (1 - (n : ℝ) * q^h ≤ (1 - q^h)^n ∧ (1 - q^h)^n ≤ allDeleted L ∧
      allDeleted L ≤ 1 ∧ 0 ≤ 1 - allDeleted L ∧ 1 - allDeleted L ≤ (n : ℝ) * q^h) ∧
    (q = 0 → allDeleted L = 1) ∧
    (0 < q → (n : ℝ) * q^h = Real.exp (Real.log (n : ℝ) + (h : ℝ) * Real.log q))) ∧
  (∀ n : ℕ, 0 < n → n ≤ 2*n ∧ 2*n ≠ n ∧
    Fintype.card (Fin n × Fin 2) = 2*n)

end SAP.P007
