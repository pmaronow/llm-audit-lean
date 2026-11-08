import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P045b
open Finset
open scoped BigOperators
noncomputable section

abbrev Assignment (n : ℕ) := Fin n → Bool

structure Design (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ w, 0 ≤ mass w
  total : ∑ w, mass w = 1

def expect {Ω K : Type*} [Fintype Ω] [CommSemiring K] (p : Ω → K) (t : Ω → K) : K :=
  ∑ ω, p ω * t ω

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

def htContrast {n : ℕ} {Δ : Type*} [DecidableEq Δ] (p : Assignment n → ℝ)
    (D : Assignment n → Fin n → Δ) (y : Fin n → Δ → ℝ)
    (k l : Δ) (z : Assignment n) : ℝ :=
  (htTotal p D y k z - htTotal p D y l z) / n

def hajek {n : ℕ} {Δ : Type*} [DecidableEq Δ] (p : Assignment n → ℝ)
    (D : Assignment n → Fin n → Δ) (y : Fin n → Δ → ℝ)
    (d : Δ) (z : Assignment n) : Option ℝ :=
  let den := ∑ i, if D z i = d then 1 / exposureProb p D i d else 0
  if den = 0 then none else some (htTotal p D y d z / den)

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

def withoutCoordinate {n : ℕ} (i : Fin (n+1)) (z : Assignment (n+1)) : Assignment n :=
  i.removeNth z

def splitAssignment {n : ℕ} (i : Fin (n+1)) : Assignment (n+1) ≃ Bool × Assignment n :=
  (Fin.insertNthEquiv (fun _ : Fin (n+1) => Bool) i).symm

def InProbability {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (p : (n : ℕ) → Ω n → ℝ) (X : (n : ℕ) → Ω n → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n => prob (p n) (fun w => ε < |X n w-a n|))
    Filter.atTop (nhds 0)

def sign (b : Bool) : ℝ := if b then 1 else -1

def signMean {n : ℕ} (z : Assignment n) : ℝ := mean (fun i => sign (z i))

def varianceFactor {n : ℕ} (z : Assignment (n+1)) : ℝ := if z 0 then 3/2 else 1/2

def varianceWitness (n : ℕ) (z : Assignment (n+1)) : ℝ := (varianceFactor z)^2/(n+1 : ℕ)

def seWitness (n : ℕ) (z : Assignment (n+1)) : ℝ := Real.sqrt (varianceWitness n z)

def regimeMean {G : ℕ} {n : Fin G → ℕ}
    (y : (g : Fin G) → Fin (n g) → Bool → Bool → ℝ) (b s : Bool) : ℝ :=
  mean (fun g => mean (fun i => y g i b s))

def baselineMean {G : ℕ} {n : Fin G → ℕ} (b : (g : Fin G) → Fin (n g) → ℝ) : ℝ :=
  mean (fun g => mean (b g))

def dilatedMarginal {G : ℕ} {n : Fin G → ℕ} (b : (g : Fin G) → Fin (n g) → ℝ)
    (g : Fin G) (i : Fin (n g)) (own high : Bool) : ℝ :=
  if high then (if own then 2 else 5/4)*b g i else (if own then 3/2 else 1)*b g i

def indirectHousehold {Nc : ℕ} (m : Fin Nc → Bool → Bool) (y : Fin Nc → Bool → Bool → ℝ) : ℝ :=
  mean (fun i => y i true (m i true)-y i false (m i false))

def contagion {Nc : ℕ} (m : Fin Nc → Bool → Bool) (y : Fin Nc → Bool → Bool → ℝ) (z : Bool) : ℝ :=
  mean (fun i => y i z (m i true)-y i z (m i false))

def otherMechanisms {Nc : ℕ} (m : Fin Nc → Bool → Bool) (y : Fin Nc → Bool → Bool → ℝ) (z : Bool) : ℝ :=
  mean (fun i => y i true (m i z)-y i false (m i z))

/-- Ordinary mean of observed outcomes in a realized exposure cell, defined only for a nonempty cell. -/
def exposureSampleMean {n : ℕ} {Δ : Type*} [DecidableEq Δ]
    (D : Assignment n → Fin n → Δ) (y : Fin n → Δ → ℝ)
    (d : Δ) (z : Assignment n) : Option ℝ :=
  let m := (univ.filter (fun i => D z i = d)).card
  if m = 0 then none else
    some ((∑ i, if D z i = d then observed D y z i else 0) / (m : ℝ))

end
end SAP.P045b
