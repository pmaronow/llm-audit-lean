import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P007

open Filter Topology
open scoped BigOperators

/-- A Boolean is true exactly when the entry is missing. The same coordinates can
represent variables or nonempty groups sharing a missingness pattern. -/
abbrev Row (h : ℕ) := Fin h → Bool
abbrev Array (n h : ℕ) := Fin n → Row h

/-- A joint probability distribution on a finite state space, with no restriction
on dependence between coordinates. -/
structure Law (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

noncomputable def probability {α : Type*} [Fintype α]
    (L : Law α) (P : α → Prop) : ℝ := by
  classical
  exact ∑ a, if P a then L.weight a else 0

noncomputable def expectation {α : Type*} [Fintype α]
    (L : Law α) (f : α → ℝ) : ℝ := ∑ a, L.weight a * f a

/-- Full mutual independence of row vectors, tested against arbitrary row events. -/
noncomputable def rowIndependent {n h : ℕ} (L : Law (Array n h)) : Prop :=
  ∀ E : Fin n → Row h → Prop,
    probability L (fun x => ∀ i, E i (x i)) =
      ∏ i, probability L (fun x => E i (x i))

noncomputable def prefixObserved {h : ℕ} (r : Row h) (j : ℕ) : Prop :=
  ∀ t : Fin h, t.val < j → r t = false

noncomputable def survival {n h : ℕ} (L : Law (Array n h))
    (i : Fin n) (j : ℕ) : ℝ := probability L (fun x => prefixObserved (x i) j)

noncomputable def allDeleted {n h : ℕ} (L : Law (Array n h)) : ℝ :=
  probability L (fun x => ∀ i, ¬ prefixObserved (x i) h)

/-- Assumption 2, or Assumption 7 for groups. The conditional ratio is asserted
only when the probability of its conditioning prefix is positive. -/
noncomputable def observationBound {n h : ℕ} (L : Law (Array n h)) (q : ℝ) : Prop :=
  0 ≤ q ∧ q < 1 ∧ ∀ i,
    (0 < h → survival L i 1 ≤ q) ∧
    ∀ j, 1 ≤ j → j < h → 0 < survival L i j →
      survival L i (j + 1) / survival L i j ≤ q

/-- Zero-based conditional coefficients for the repaired product formula.
At a null prefix this explicitly defines a coefficient of zero, rather than a
conditional probability given that null event. -/
noncomputable def conditionalObserved {n h : ℕ} (L : Law (Array n h))
    (i : Fin n) (j : ℕ) : ℝ :=
  if 0 < survival L i j then survival L i (j + 1) / survival L i j else 0

noncomputable def superlog (h : ℕ → ℕ) : Prop :=
  Tendsto (fun n : ℕ => (h n : ℝ) / Real.log (n : ℝ)) atTop atTop

/-- Equality of the row-vector distributions, without an independence condition. -/
noncomputable def sameRowLaw {n h : ℕ} (L : Law (Array n h)) : Prop :=
  ∀ (i j : Fin n) (E : Row h → Prop),
    probability L (fun x => E (x i)) = probability L (fun x => E (x j))

noncomputable def deletedIndicator {n h : ℕ} (x : Array n h) (i : Fin n) : ℝ := by
  classical
  exact if prefixObserved (x i) h then 0 else 1

/-- Used only for positive row counts in the Challenge statements. -/
noncomputable def deletedFraction {n h : ℕ} (x : Array n h) : ℝ :=
  (∑ i, deletedIndicator x i) / n

noncomputable def lowerBound (n : ℕ) (q : ℝ) (h : ℕ) : ℝ := (1 - q ^ h) ^ n
noncomputable def fractionBound (q : ℝ) (h : ℕ) : ℝ := 1 - q ^ h

/-- The inverse threshold is used only for n>0, 0<q<1 and 0<a<1. -/
noncomputable def realThreshold (n : ℕ) (q a : ℝ) : ℝ :=
  Real.log (1 - a ^ ((n : ℝ)⁻¹)) / Real.log q

noncomputable def realLowerBound (n : ℕ) (q x : ℝ) : ℝ := (1 - q ^ x) ^ n

/-- Explicit weights for independent cells with observation chances a_ij.
Statements using these weights also require an actual normalized Law. -/
noncomputable def cellWeights {n h : ℕ} (a : Fin n → Fin h → ℝ)
    (x : Array n h) : ℝ := ∏ i, ∏ j, if x i j then 1 - a i j else a i j

noncomputable def equalWeights (n h : ℕ) (q : ℝ) : Array n h → ℝ :=
  cellWeights (fun _ _ => q)

noncomputable def unequalWeights (n h : ℕ) : Array n h → ℝ :=
  cellWeights (fun _ j => if j.val = 0 then (3/4 : ℝ) else 1/4)

noncomputable def nullFirstWeights (x : Array 1 2) : ℝ := by
  classical
  exact ∏ i, if x i = (fun j : Fin 2 => decide (j.val = 0)) then 1 else 0

noncomputable def fullyMissingWeights (x : Array 1 2) : ℝ := by
  classical
  exact ∏ i, if x i = (fun _ : Fin 2 => true) then 1 else 0

noncomputable def laterNullWeights (x : Array 2 3) : ℝ := by
  classical
  exact ∏ i, ((1/2 : ℝ) * (if x i = (fun j : Fin 3 => decide (j.val = 0)) then 1 else 0) +
    (1 - (1/2 : ℝ)) * (if x i = (fun j : Fin 3 => decide (j.val = 1)) then 1 else 0))

noncomputable def figure5Weights : Array 2 2 → ℝ :=
  cellWeights (fun _ => ![(3/4 : ℝ), 1/2])

noncomputable def nonidenticalWeights : Array 2 1 → ℝ :=
  cellWeights (fun i _ => ![(1/4 : ℝ), 1/2] i)

/-- Fixed arrays for uniform column subsampling: a row is its observed column set. -/
abbrev ObservedArray (n K : ℕ) := Fin n → Finset (Fin K)

noncomputable def sampleSets (K k : ℕ) : Finset (Finset (Fin K)) :=
  Finset.univ.powersetCard k

noncomputable def retainedShare {n K : ℕ} (m : ObservedArray n K)
    (S : Finset (Fin K)) : ℝ := by
  classical
  exact (∑ i, if S ⊆ m i then (1 : ℝ) else 0) / n

/-- The finite uniform average; statements require n>0 and k≤K so this is a
mean over a nonempty sample space with a positive row denominator. -/
noncomputable def meanRetained {n K : ℕ} (m : ObservedArray n K) (k : ℕ) : ℝ :=
  (∑ S ∈ sampleSets K k, retainedShare m S) / (sampleSets K k).card

noncomputable def meanLoss {n K : ℕ} (m : ObservedArray n K) (k : ℕ) : ℝ :=
  1 - meanRetained m k

noncomputable def missingAverage {n : ℕ} {J : Type*} [Fintype J]
    (m : Fin n → J → Bool) : ℝ :=
  (∑ j, (∑ i, if m i j then (1 : ℝ) else 0) / n) / Fintype.card J

noncomputable def missingCount {n : ℕ} {J : Type*} [Fintype J]
    (m : Fin n → J → Bool) : ℕ := ∑ j, ∑ i, if m i j then 1 else 0

def observedColumns {n K : ℕ} (m : Fin n → Fin K → Bool) : ObservedArray n K :=
  fun i => Finset.univ.filter (fun j => m i j = false)

end SAP.P007
