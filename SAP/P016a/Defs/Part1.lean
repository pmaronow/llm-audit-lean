import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016a
open scoped BigOperators
open Finset

abbrev Outcome (n : ℕ) := Fin n → ℝ

abbrev Assignment (n : ℕ) := Fin n → Bool

def bit (b : Bool) : ℝ := if b then 1 else 0

def groupSize {n : ℕ} (z : Assignment n) (g : Bool) : ℕ :=
  ∑ i, if z i = g then 1 else 0

noncomputable def groupSum {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) : ℝ :=
  ∑ i, if z i = g then u i else 0

noncomputable def groupMean {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) : ℝ :=
  groupSum u z g / groupSize z g

noncomputable def pooledMean {n : ℕ} (u : Outcome n) : ℝ := (∑ i, u i) / n

noncomputable def tss {n : ℕ} (u : Outcome n) : ℝ := ∑ i, (u i - pooledMean u)^2

noncomputable def rss {n : ℕ} (u : Outcome n) (z : Assignment n) : ℝ :=
  ∑ i, (u i - groupMean u z (z i))^2

noncomputable def meanDifference {n : ℕ} (u : Outcome n) (z : Assignment n) : ℝ :=
  groupMean u z true - groupMean u z false

noncomputable def ecdf {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) (t : ℝ) : ℝ :=
  (∑ i, if z i = g ∧ u i ≤ t then (1 : ℝ) else 0) / groupSize z g

noncomputable def ks {n : ℕ} (u : Outcome n) (z : Assignment n) : ℝ :=
  (List.ofFn fun i => |ecdf u z true (u i) - ecdf u z false (u i)|).foldr max 0

noncomputable def signedKS {n : ℕ} (u : Outcome n) (z : Assignment n) : ℝ :=
  (List.ofFn fun i => ecdf u z true (u i) - ecdf u z false (u i)).foldr max 0

noncomputable def additiveAdjust {n : ℕ} (Y : Outcome n) (Z : Assignment n) (t : ℝ) : Outcome n :=
  fun i => Y i - bit (Z i) * t

noncomputable def additiveGenerate {n : ℕ} (y : Outcome n) (z : Assignment n) (t : ℝ) : Outcome n :=
  fun i => y i + bit (z i) * t

structure FiniteLaw (Ω : Type) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

noncomputable def mass {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (E : Ω → Prop) : ℝ :=
  by classical exact ∑ ω, if E ω then P.weight ω else 0

noncomputable def expectation {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, P.weight ω * f ω

noncomputable def covariance {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (f g : Ω → ℝ) : ℝ :=
  expectation P (fun ω => f ω * g ω) - expectation P f * expectation P g

noncomputable def variance {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  covariance P f f

noncomputable def upperP {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (s : Ω → ℝ) (z : Ω) : ℝ :=
  mass P (fun w => s z ≤ s w)

noncomputable def lowerP {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (s : Ω → ℝ) (z : Ω) : ℝ :=
  mass P (fun w => s w ≤ s z)

noncomputable def doubledP (L U : ℝ) : ℝ := min 1 (2 * min L U)

noncomputable def uniformLaw (Ω : Type) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight := fun _ => 1 / Fintype.card Ω
  nonneg := fun _ => by positivity
  total := by simp [div_eq_mul_inv, Fintype.card_ne_zero]

def complete4 : Fin 6 → Assignment 4 :=
  ![![true,true,false,false], ![true,false,true,false], ![true,false,false,true],
    ![false,true,true,false], ![false,true,false,true], ![false,false,true,true]]

def blocked4 : Fin 4 → Assignment 4 :=
  ![![true,true,false,false], ![true,false,false,true],
    ![false,true,true,false], ![false,false,true,true]]

def u4 : Outcome 4 := ![0,1,2,3]

noncomputable def lsObjective {n k : ℕ} (u : Outcome n) (X : Fin n → Fin k → ℝ)
    (b : Fin k → ℝ) : ℝ := ∑ i, (u i - ∑ j, X i j * b j)^2

noncomputable def fitted {n k : ℕ} (X : Fin n → Fin k → ℝ) (b : Fin k → ℝ) : Outcome n :=
  fun i => ∑ j, X i j * b j

noncomputable def lsRSS {n k : ℕ} (u : Outcome n) (X : Fin n → Fin k → ℝ) : ℝ :=
  sInf (Set.range (lsObjective u X))

noncomputable def treatedNeighbors {n : ℕ} (S : Fin n → Fin n → ℝ)
    (z : Assignment n) (i : Fin n) : ℝ := ∑ j, bit (z j) * S j i

noncomputable def degree {n : ℕ} (S : Fin n → Fin n → ℝ) (i : Fin n) : ℝ := ∑ j, S j i

noncomputable def networkX {n : ℕ} (S : Fin n → Fin n → ℝ) (z : Assignment n) :
    Fin n → Fin 4 → ℝ := fun i => ![1,bit (z i),treatedNeighbors S z i,degree S i]

noncomputable def basicX {n : ℕ} (z : Assignment n) : Fin n → Fin 2 → ℝ :=
  fun i => ![1,bit (z i)]

noncomputable def groupValues {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) : Multiset ℝ :=
  ((Finset.univ.filter (fun i => z i = g)).val).map u

def sameMargins {n : ℕ} (u : Outcome n) (z : Assignment n) (v : Outcome n) (w : Assignment n) : Prop :=
  ∀ g, groupValues u z g = groupValues v w g

noncomputable def pairedCovariance2 (t c : Outcome 2) : ℝ :=
  ((t 0 - (t 0+t 1)/2)*(c 0 - (c 0+c 1)/2) +
    (t 1 - (t 0+t 1)/2)*(c 1 - (c 0+c 1)/2))/2

end SAP.P016a
