import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def Admissible {C : Type*} [MeasurableSpace C] (π : C → ℝ) : Prop :=
  Measurable π ∧ ∀ x, 0 ≤ π x ∧ π x ≤ 1

def bit (t : Bool) : ℝ := if t then 1 else 0

def treatedCount {n : ℕ} (T : Fin n → Bool) : ℝ := ∑ i, bit (T i)

def wATO {n : ℕ} (T : Fin n → Bool) (Y : Fin n → ℝ) : ℝ :=
  if 0 < treatedCount T then (∑ i, Y i * bit (T i)) / treatedCount T else 0

def wATT {C : Type*} {n : ℕ} (μhat : C → ℝ) (X : Fin n → C)
    (T : Fin n → Bool) (Y : Fin n → ℝ) : ℝ :=
  wATO T (fun i => Y i - μhat (X i))

def wWeightedTT {C : Type*} {n : ℕ} (μhat g : C → ℝ) (X : Fin n → C)
    (T : Fin n → Bool) (Y : Fin n → ℝ) : ℝ :=
  ∑ i, (Y i - μhat (X i)) * bit (T i) * g (X i)

def wTT {C : Type*} {n : ℕ} (μhat : C → ℝ) (X : Fin n → C)
    (T : Fin n → Bool) (Y : Fin n → ℝ) : ℝ :=
  wWeightedTT μhat (fun _ => 1) X T Y

def IsBest {P : Type*} (PiSet : Set P) (f : P → ℝ) (π : P) : Prop :=
  π ∈ PiSet ∧ ∀ π' ∈ PiSet, f π' ≤ f π

def bestValue {P : Type*} (PiSet : Set P) (f : P → ℝ) : ℝ := sSup (f '' PiSet)

def regret {P : Type*} (PiSet : Set P) (V : P → ℝ) (π : P) : ℝ :=
  bestValue PiSet V - V π

def positiveRule {C : Type*} (m : C → ℝ) : C → ℝ :=
  fun x => if 0 < m x then 1 else 0

def printedAverageRule {C : Type*} (m : C → ℝ) : C → ℝ :=
  fun x => if (∀ z, m z ≤ m x) ∧ 0 < m x then 1 else 0

def emptyFactor (n : ℕ) (q : ℝ) : ℝ := ∑ j ∈ Finset.range n, (1 - q) ^ j

abbrev BinaryPolicy := ℝ × ℝ

def binaryRule (p : BinaryPolicy) : Bool → ℝ := fun x => if x then p.2 else p.1

def binaryFeasible (p : BinaryPolicy) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

def binaryPolicies : Set BinaryPolicy := {p | binaryFeasible p}

def coinMass (q : ℝ) (t : Bool) : ℝ := if t then q else 1 - q

def twoATO (p : ℝ) (m : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∑ x0 : Bool, ∑ x1 : Bool, ∑ t0 : Bool, ∑ t1 : Bool,
    coinMass p x0 * coinMass p x1 *
      coinMass (binaryRule π x0) t0 * coinMass (binaryRule π x1) t1 *
      wATO ![t0, t1] ![m x0, m x1]

def oneTT (y1 : Bool → ℝ) (est : Bool → Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∑ x : Bool, ∑ t : Bool,
    (1 / 2 : ℝ) * coinMass (binaryRule π x) t *
      wTT (est x) ![x] ![t] ![y1 x]

def binaryWelfare (p : ℝ) (τ : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  (1 - p) * π.1 * τ false + p * π.2 * τ true

def outcomeP1 (x : Bool) : ℝ := if x then 1 else 0

def effectP1 (β : ℝ) (x : Bool) : ℝ := if x then 1-β else 1

def rewardP1 (p : ℝ) (π : BinaryPolicy) : ℝ := twoATO p outcomeP1 π

def eventMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Set Ω) (f : Ω → ℝ) : ℝ :=
  (∫ ω in s, f ω ∂μ) / (μ s).toReal

def finiteMass {K : ℕ} (p π : Fin K → ℝ) : ℝ := ∑ i, p i * π i

def finiteA {K : ℕ} (p m π : Fin K → ℝ) : ℝ := ∑ i, p i * m i * π i

end
end SAP.P006b
