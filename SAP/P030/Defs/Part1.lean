import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P030
open scoped BigOperators
noncomputable section

/-- Binary assignments, with zero-based unit indices. -/
abbrev Assignment (N : ℕ) := Fin N → Bool
abbrev AssignmentSet (N : ℕ) := Finset (Assignment N)
abbrev FixedIndicator (N : ℕ) := Fin N → Bool
abbrev PotentialOutcomes (N : ℕ) := Fin N → Assignment N → ℝ

def treatment {N : ℕ} (z : Assignment N) (i : Fin N) : ℝ := if z i then 1 else 0

/-- Assignments agreeing with the observation at every fixed unit. -/
def conditionalAssignments {N : ℕ} (Ω : AssignmentSet N)
    (S : FixedIndicator N) (obs : Assignment N) : Finset (Assignment N) := by
  classical
  exact Ω.filter (fun z => ∀ i, S i = true → z i = obs i)

def NoEffects {N : ℕ} (Ω : AssignmentSet N) (Y : PotentialOutcomes N) : Prop :=
  ∀ i, ∀ z ∈ Ω, ∀ z' ∈ Ω, Y i z = Y i z'

/-- The same unit, with the same treatment, has the same outcome. -/
def NoInterference {N : ℕ} (Ω : AssignmentSet N) (Y : PotentialOutcomes N) : Prop :=
  ∀ i, ∀ z ∈ Ω, ∀ z' ∈ Ω, z i = z' i → Y i z = Y i z'

def FixedOutcomeNull {N : ℕ} (Ω' : AssignmentSet N)
    (S : FixedIndicator N) (Y : PotentialOutcomes N) : Prop :=
  ∀ i, S i = true → ∀ z ∈ Ω', ∀ z' ∈ Ω', Y i z = Y i z'

def fixedOutcomes {N : ℕ} (S : FixedIndicator N) (Y : PotentialOutcomes N)
    (z : Assignment N) : {i // S i = true} → ℝ := fun i => Y i.val z

def statistic {N : ℕ} (S : FixedIndicator N) (Y : PotentialOutcomes N)
    (g : ({i // S i = true} → ℝ) → Assignment N → ℝ) (z : Assignment N) : ℝ :=
  g (fixedOutcomes S Y z) z

def referenceStatistic {N : ℕ} (S : FixedIndicator N) (Y : PotentialOutcomes N)
    (g : ({i // S i = true} → ℝ) → Assignment N → ℝ)
    (obs z : Assignment N) : ℝ := g (fixedOutcomes S Y obs) z

/-- A probability law with an explicit finite support. -/
structure FiniteLaw (A : Type*) where
  support : Finset A
  mass : A → ℝ
  nonneg : ∀ z ∈ support, 0 ≤ mass z
  total : ∑ z ∈ support, mass z = 1

def probability {A : Type*} (μ : FiniteLaw A) (P : A → Prop) : ℝ := by
  classical
  exact ∑ z ∈ μ.support, if P z then μ.mass z else 0

def lowerTail {A : Type*} (μ : FiniteLaw A) (f : A → ℝ) (x : ℝ) : ℝ :=
  probability μ (fun z => f z ≤ x)

def upperTail {A : Type*} (μ : FiniteLaw A) (f : A → ℝ) (x : ℝ) : ℝ :=
  probability μ (fun z => x ≤ f z)

/-- Uniform assignment probability; all uses require nonempty support. -/
def uniformProbability {A : Type*} (Ω : Finset A) (P : A → Prop) : ℝ := by
  classical
  exact ((Ω.filter P).card : ℝ) / (Ω.card : ℝ)

def uniformLaw {A : Type*} (Ω : Finset A) (hΩ : Ω.Nonempty) : FiniteLaw A where
  support := Ω
  mass := fun _ => (Ω.card : ℝ)⁻¹
  nonneg := by intros; positivity
  total := by
    have hn : (Ω.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hΩ)
    simp [hn]

def printedReject (α p : ℝ) : Prop := p < α / 2 ∨ 1 - α / 2 < p
def correctedReject (α pL pU : ℝ) : Prop := pL < α / 2 ∨ pU < α / 2
def twoTailP (pL pU : ℝ) : ℝ := min 1 (2 * min pL pU)

/-- Midranks retain multiplicities of ties. -/
def averageRank {n : ℕ} (a : Fin n → ℝ) (k : Fin n) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun l => a l < a k)).card : ℝ) +
    (((Finset.univ.filter (fun l => a l = a k)).card : ℝ) + 1) / 2

def centeredRanks {n : ℕ} (a : Fin n → ℝ) (k : Fin n) : ℝ :=
  averageRank a k - ((n : ℝ) + 1) / 2
def rankCross {n : ℕ} (a b : Fin n → ℝ) : ℝ := ∑ k, centeredRanks a k * centeredRanks b k
def rankSquares {n : ℕ} (a : Fin n → ℝ) : ℝ := ∑ k, centeredRanks a k ^ 2
def spearman {n : ℕ} (a b : Fin n → ℝ) : ℝ :=
  rankCross a b / Real.sqrt (rankSquares a * rankSquares b)
def rankCov {n : ℕ} (m : ℝ) (a b : Fin n → ℝ) : ℝ := rankCross a b / m
def printedRho {n : ℕ} (m : ℝ) (a b : Fin n → ℝ) : ℝ :=
  rankCov m a b / ((rankSquares a / m) * (rankSquares b / m))
def Nonconstant {n : ℕ} (a : Fin n → ℝ) : Prop := ∃ i j, a i ≠ a j

/-- Nearest treated variant unit; the statements use only nonempty treated sets. -/
def nearestDistance {N : ℕ} (x : Fin N → ℝ) (S : FixedIndicator N)
    (z : Assignment N) (i : Fin N) : ℝ := by
  classical
  let V := Finset.univ.filter (fun j => S j = false ∧ z j = true)
  exact if h : V.Nonempty then V.inf' h (fun j => |x i - x j|) else 0

end
end SAP.P030
