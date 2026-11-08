import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a
noncomputable section

abbrev Assignment (n : ℕ) := Fin n → Bool

structure Design (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ w, 0 ≤ mass w
  total : ∑ w, mass w = 1

def expect {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ w, p w * X w

def prob {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  by classical exact expect p (fun w => if E w then 1 else 0)

def condMean {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (E : Ω → Prop) (X : Ω → ℝ) : ℝ :=
  by classical exact expect p (fun w => if E w then X w else 0) / prob p E

def variance {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  expect p (fun w => (X w - expect p X)^2)

def average {Ω : Type*} (S : Finset Ω) (X : Ω → ℝ) : ℝ :=
  (∑ w ∈ S, X w) / S.card

def mean {I : Type*} [Fintype I] (x : I → ℝ) : ℝ :=
  (∑ i, x i) / Fintype.card I

def bit (b : Bool) : ℝ := if b then 1 else 0

def bernoulli {n : ℕ} (p : ℝ) (z : Assignment n) : ℝ :=
  ∏ i, if z i then p else 1-p

def fixedAssignments (n k : ℕ) : Finset (Assignment n) :=
  univ.filter (fun z => (univ.filter (fun i => z i = true)).card = k)

inductive Exposure | d11 | d10 | d01 | d00
  deriving DecidableEq

instance : Fintype Exposure := ⟨{.d11, .d10, .d01, .d00}, by
  intro d; cases d <;> simp⟩

structure Network (n : ℕ) where
  adj : Fin n → Fin n → Bool
  symmetric : ∀ i j, adj i j = adj j i
  loopless : ∀ i, adj i i = false

def exposure {n : ℕ} (A : Fin n → Fin n → Bool) (z : Assignment n)
    (i : Fin n) : Exposure :=
  if z i then
    if ∃ j, A i j = true ∧ z j = true then .d11 else .d10
  else if ∃ j, A i j = true ∧ z j = true then .d01 else .d00

def exposureProb {n : ℕ} {Δ : Type*} [DecidableEq Δ] (p : Assignment n → ℝ)
    (D : Assignment n → Fin n → Δ) (i : Fin n) (d : Δ) : ℝ :=
  prob p (fun z => D z i = d)

def observed {n : ℕ} {Δ : Type*} [DecidableEq Δ] (D : Assignment n → Fin n → Δ)
    (y : Fin n → Δ → ℝ) (z : Assignment n) (i : Fin n) : ℝ := y i (D z i)

def htTotal {n : ℕ} {Δ : Type*} [DecidableEq Δ] (p : Assignment n → ℝ)
    (D : Assignment n → Fin n → Δ) (y : Fin n → Δ → ℝ)
    (d : Δ) (z : Assignment n) : ℝ :=
  ∑ i, if D z i = d then observed D y z i / exposureProb p D i d else 0

def effect {n : ℕ} {Δ : Type*} [DecidableEq Δ] (y : Fin n → Δ → ℝ) (k l : Δ) : ℝ :=
  mean (fun i => y i k) - mean (fun i => y i l)

def treatedCount {n : ℕ} (z : Assignment n) : ℕ :=
  (univ.filter (fun i => z i = true)).card

def marginal {n : ℕ} (p : Assignment n → ℝ)
    (y : Fin n → Assignment n → ℝ) (i : Fin n) (b : Bool) : ℝ :=
  condMean p (fun z => z i = b) (y i)

def armMean {n : ℕ} (y : Fin n → Assignment n → ℝ)
    (b : Bool) (z : Assignment n) : ℝ :=
  (∑ i, if z i = b then y i z else 0) /
    (∑ i, if z i = b then (1 : ℝ) else 0)

def armExists {n : ℕ} (b : Bool) (z : Assignment n) : Prop :=
  ∃ i, z i = b

def groupOverall {n : ℕ} (y : Fin n → Assignment n → ℝ) (z : Assignment n) : ℝ :=
  mean (fun i => y i z)

def coMembers {n : ℕ} (i : Fin n) (z : Assignment n) : ℝ :=
  ∑ j ∈ univ.erase i, bit (z j)

abbrev BernoulliWitnessOutcome := Bool × Assignment 4 × Assignment 4

def witnessHigh (w : BernoulliWitnessOutcome) : Assignment 4 :=
  if w.1 then w.2.1 else w.2.2

def witnessLow (w : BernoulliWitnessOutcome) : Assignment 4 :=
  if w.1 then w.2.2 else w.2.1

def bernoulliWitnessMass (w : BernoulliWitnessOutcome) : ℝ :=
  (1/2) * bernoulli (1/2) (witnessHigh w) * bernoulli (1/4) (witnessLow w)

def witnessArm (b : Bool) (high : Bool) (w : BernoulliWitnessOutcome) : ℝ :=
  armMean coMembers b (if high then witnessHigh w else witnessLow w)

def witnessDomain (b : Bool) (high : Bool) (w : BernoulliWitnessOutcome) : Prop :=
  armExists b (if high then witnessHigh w else witnessLow w)

def witnessDirect (high : Bool) (w : BernoulliWitnessOutcome) : ℝ :=
  witnessArm true high w - witnessArm false high w

def witnessIndirect (w : BernoulliWitnessOutcome) : ℝ :=
  witnessArm false true w - witnessArm false false w

def witnessTotal (w : BernoulliWitnessOutcome) : ℝ :=
  witnessArm true true w - witnessArm false false w

def witnessOverall (w : BernoulliWitnessOutcome) : ℝ :=
  groupOverall coMembers (witnessHigh w) - groupOverall coMembers (witnessLow w)

def groupHT {n : ℕ} (p : ℝ) (y : Fin n → Assignment n → ℝ)
    (b : Bool) (z : Assignment n) : ℝ :=
  (∑ i, if z i = b then y i z else 0) / ((n : ℝ) * (if b then p else 1-p))

def firstStageSets (G C : ℕ) : Finset (Finset (Fin G)) := univ.powersetCard C

abbrev GroupAssignments {G : ℕ} (n : Fin G → ℕ) := (g : Fin G) → Assignment (n g)

def selectedLaw {G : ℕ} (n : Fin G → ℕ) (C : ℕ)
    (q : (g : Fin G) → Assignment (n g) → ℝ)
    (w : Finset (Fin G) × GroupAssignments n) : ℝ :=
  if w.1 ∈ firstStageSets G C then
    (1 / (firstStageSets G C).card) * ∏ g, q g (w.2 g) else 0

def selectedMean {G : ℕ} {n : Fin G → ℕ} (C : ℕ)
    (X : (g : Fin G) → Assignment (n g) → ℝ)
    (w : Finset (Fin G) × GroupAssignments n) : ℝ :=
  (∑ g ∈ w.1, X g (w.2 g)) / C

def crMass (n k : ℕ) (z : Assignment n) : ℝ :=
  if z ∈ fixedAssignments n k then 1 / (fixedAssignments n k).card else 0

def rawSampleVar {I : Type*} (S : Finset I) (x : I → ℝ) : ℝ :=
  (∑ i ∈ S, (x i - average S x)^2) / ((S.card : ℝ)-1)

def popVar {I : Type*} [Fintype I] (x : I → ℝ) : ℝ := rawSampleVar univ x

def treatedSet {n : ℕ} (z : Assignment n) : Finset (Fin n) := univ.filter (fun i => z i = true)

def directGroup {n : ℕ} (a b : Fin n → ℝ) (z : Assignment n) : ℝ :=
  average (treatedSet z) a - average (univ \ treatedSet z) b

def droppedWithin {n : ℕ} (a b : Fin n → ℝ) (z : Assignment n) : ℝ :=
  (if 2 ≤ (treatedSet z).card then rawSampleVar (treatedSet z) a / (treatedSet z).card else 0) +
  (if 2 ≤ (univ \ treatedSet z).card then
    rawSampleVar (univ \ treatedSet z) b / (univ \ treatedSet z).card else 0)

def directVarianceEstimate {G : ℕ} {n : Fin G → ℕ} (C : ℕ)
    (a b : (g : Fin G) → Fin (n g) → ℝ)
    (w : Finset (Fin G) × GroupAssignments n) : ℝ :=
  ((1 - (C : ℝ)/G)/C) * rawSampleVar w.1 (fun g => directGroup (a g) (b g) (w.2 g)) +
    (∑ g ∈ w.1, droppedWithin (a g) (b g) (w.2 g)) / ((C : ℝ)*G)

def requiredDirectVariance {G : ℕ} {n : Fin G → ℕ} (C : ℕ)
    (a b : (g : Fin G) → Fin (n g) → ℝ)
    (w : Finset (Fin G) × GroupAssignments n) : Option ℝ :=
  if 2 ≤ C ∧ w.1.card=C ∧ ∀ g ∈ w.1,
    2 ≤ (treatedSet (w.2 g)).card ∧ 2 ≤ (univ \ treatedSet (w.2 g)).card
  then some (directVarianceEstimate C a b w) else none

def neighborhood {n : ℕ} (A : Fin n → Fin n → Bool) (i : Fin n) : Finset (Fin n) :=
  insert i (univ.filter (fun j => A i j = true))

def neighborhoodCount {n : ℕ} (A : Fin n → Fin n → Bool)
    (z : Assignment n) (i : Fin n) : ℕ :=
  ((neighborhood A i).filter (fun j => z j = true)).card

end
end SAP.P045a
