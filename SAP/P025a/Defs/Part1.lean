import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a
noncomputable section
open scoped BigOperators

/-! Indices are zero based; a cut is the number of entries in the prefix.
The endpoint definitions below are used only for nonempty finite samples,
positive masses, and positive ordered probability bounds. -/

def populationMean {n : ℕ} (y : Fin n → ℝ) : ℝ := (∑ i, y i) / n

def ratio {ι : Type*} [Fintype ι] (y a w : ι → ℝ) : ℝ :=
  (∑ i, a i * w i * y i) / (∑ i, a i * w i)

def weightBox {ι : Type*} (α β : ℝ) (w : ι → ℝ) : Prop :=
  ∀ i, 1 / β ≤ w i ∧ w i ≤ 1 / α

def normBox {ι : Type*} (γ : ℝ) (w : ι → ℝ) : Prop :=
  ∀ i, 1 ≤ w i ∧ w i ≤ γ

def lowerWeights {n : ℕ} (γ : ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => if i.val < k then γ else 1

def upperWeights {n : ℕ} (γ : ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => if i.val < k then 1 else γ

def lowerValue {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : ℕ) : ℝ :=
  ratio y a (lowerWeights γ k)

def upperValue {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : ℕ) : ℝ :=
  ratio y a (upperWeights γ k)

def lowerCut {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : Fin n) : Prop :=
  IsLeast {j : Fin n | lowerValue y a γ j.val ≤ y j} k

def upperCut {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : Fin n) : Prop :=
  IsLeast {j : Fin n | upperValue y a γ j.val ≤ y j} k

def printedLowerCut {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : Fin n) : Prop :=
  IsLeast {j : Fin n | y j ≤ lowerValue y a γ j.val} k

def attainable {ι : Type*} [Fintype ι] (y a : ι → ℝ) (α β : ℝ) : Set ℝ :=
  {v | ∃ w, weightBox α β w ∧ ratio y a w = v}

def normAttainable {ι : Type*} [Fintype ι] (y a : ι → ℝ) (γ : ℝ) : Set ℝ :=
  {v | ∃ w, normBox γ w ∧ ratio y a w = v}

def lowerEndpoint {ι : Type*} [Fintype ι] (y a : ι → ℝ) (α β : ℝ) : ℝ :=
  sInf (attainable y a α β)

def upperEndpoint {ι : Type*} [Fintype ι] (y a : ι → ℝ) (α β : ℝ) : ℝ :=
  sSup (attainable y a α β)

def separation {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) : Prop :=
  ∀ k : Fin n, y k ≠ upperValue y a γ k.val ∧ y k ≠ lowerValue y a γ k.val

def binaryTwo : Fin 2 → ℝ := ![0, 1]

def twoPi : Fin 2 → ℝ := ![1/2, 1]

def fourOutcomes : Fin 4 → ℝ := ![0, 1, 2, 3]

/-- The literal printed tail is undefined when its lower limit is not a class index. -/
def printedLowerExpression {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : ℕ) : Option ℝ :=
  if 2 ≤ k ∧ k ≤ n then some
    ((γ * (∑ i with i.val < k, a i * y i) + (∑ i with k-2 ≤ i.val, a i * y i)) /
     (γ * (∑ i with i.val < k, a i) + (∑ i with k-2 ≤ i.val, a i))) else none

def lowerNumerator {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : ℕ) : ℝ :=
  γ * (∑ i with i.val < k, a i * y i) + ∑ i with k ≤ i.val, a i * y i

def lowerDenominator {n : ℕ} (a : Fin n → ℝ) (γ : ℝ) (k : ℕ) : ℝ :=
  γ * (∑ i with i.val < k, a i) + ∑ i with k ≤ i.val, a i

/-- Plain finite sampling data, with normalization asserted in the witness theorem. -/
def twoSample (ω : Fin 2) : Finset (Fin 2) := if ω = 0 then {1} else {0, 1}

def twoProbability (_ : Fin 2) : ℝ := 1/2

def designInclusion {ι κ : Type*} [Fintype κ]
    (sample : κ → Finset ι) (probability : κ → ℝ) (i : ι) : ℝ := by
  classical
  exact ∑ ω, probability ω * (if i ∈ sample ω then 1 else 0)

def sixTailOutcomes : Fin 6 → ℝ := ![0, 0, 1, 1, 2, 3]

def sixTailClass : Fin 6 → Fin 4 := ![0, 0, 1, 1, 2, 3]

def fourClassSample (ω : Fin 2 × Fin 2) : Finset (Fin 6) :=
  {⟨ω.1.val, by omega⟩, ⟨ω.2.val+2, by omega⟩, 4, 5}

def fourClassProbability (_ : Fin 2 × Fin 2) : ℝ := 1/4

def designClassTotal {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (sample : κ → Finset ι) (probability : κ → ℝ) (cls : ι → Fin J) (j : Fin J) : ℝ :=
  ∑ i with cls i = j, designInclusion sample probability i

def binaryLower (p γ : ℝ) : ℝ := p / (γ * (1-p) + p)

def binaryUpper (p γ : ℝ) : ℝ := γ * p / ((1-p) + γ * p)

def binaryInterval (p γ : ℝ) : Set ℝ := Set.Icc (binaryLower p γ) (binaryUpper p γ)

def reweightedPrevalence (p π₁ π₀ : ℝ) : ℝ :=
  (p/π₁) / (p/π₁ + (1-p)/π₀)

def sampleOddsRatio (pG pE : ℝ) : ℝ := pG * (1-pE) / ((1-pG) * pE)

def quotaDraws (N s : ℕ) : Finset (Finset (Fin N)) := Finset.univ.powersetCard s

def quotaMarginal (N s : ℕ) (i : Fin N) : ℝ :=
  ((quotaDraws N s).filter (fun t => i ∈ t)).card / ((quotaDraws N s).card : ℝ)

def applicationStrata : List (ℕ × ℕ) :=
  [(48,44), (16,4), (864,291), (288,288), (12,4), (1156,291), (289,288)]

def pairObjective (c₁ c₂ p q u v x z : ℝ) : ℝ :=
  (c₁ + x*p*u + z*q*v) / (c₂ + x*p + z*q)

end
end SAP.P025a
