import Mathlib
import SAP.P016a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016a
open scoped BigOperators
open Finset

noncomputable def exposureSum {n : ℕ} (S : Fin n → Fin n → ℝ) (z : Assignment n)
    (i : Fin n) : ℝ := ∑ j, S i j * bit (z j)

noncomputable def similarity {n : ℕ} (s : Fin n → Option ℝ) (i j : Fin n) : ℝ :=
  if i = j then 0 else match s i, s j with
  | some a, some b => 1 - |a-b|/2
  | _, _ => 0

noncomputable def distance {n : ℕ} (s : Outcome n) (i j : Fin n) : ℝ := |s i-s j|

noncomputable def conditionalMean {n : ℕ} {Ω : Type} [Fintype Ω] (S : Fin n → Fin n → ℝ)
    (bank : Ω → Assignment n) (i : Fin n) (a : Bool) : ℝ :=
  (∑ b, if bank b i = a then exposureSum S (bank b) i else 0) /
    (∑ b, if bank b i = a then (1 : ℝ) else 0)

noncomputable def centeredExposure {n : ℕ} {Ω : Type} [Fintype Ω] (S : Fin n → Fin n → ℝ)
    (bank : Ω → Assignment n) (z : Assignment n) : Outcome n :=
  fun i => exposureSum S z i - bit (z i)*conditionalMean S bank i true -
    (1-bit (z i))*conditionalMean S bank i false

noncomputable def sampleVariance {n : ℕ} (h : Outcome n) : ℝ :=
  (∑ i, (h i-pooledMean h)^2) / ((n : ℝ)-1)

noncomputable def sampleSD {n : ℕ} (h : Outcome n) : ℝ := Real.sqrt (sampleVariance h)

noncomputable def standardize {n : ℕ} (h : Outcome n) : Outcome n :=
  fun i => (h i-pooledMean h) / sampleSD h

noncomputable def codedExposure {n N : ℕ} (S : Fin n → Fin n → ℝ)
    (bank : Fin N → Assignment n) (z : Assignment n) : Outcome n :=
  standardize (centeredExposure S bank z)

noncomputable def applicationAdjust {n : ℕ} (Y : Outcome n) (Z : Assignment n)
    (e : Outcome n) (b1 b2 : ℝ) : Outcome n := fun i => Y i-bit (Z i)*b1-b2*e i

noncomputable def applicationX {n : ℕ} (z : Assignment n) (e : Outcome n) :
    Fin n → Fin 3 → ℝ := fun i => ![1,bit (z i),e i]

def printedReject (p : ℝ) : Prop := p < 1/20

def codedReject (p : ℝ) : Prop := p ≤ 1/20

def matchedBank4 : Fin 4 → Assignment 4 :=
  ![![false,true,false,true], ![false,true,true,false],
    ![true,false,false,true], ![true,false,true,false]]

def matchedBank6 (b : Fin 3 → Bool) : Assignment 6 :=
  ![b 0, !(b 0), b 1, !(b 1), b 2, !(b 2)]

noncomputable def scores4 : Outcome 4 := ![-1,-1/2,1/2,1]

noncomputable def scores6 : Outcome 6 := ![-1,-3/4,-1/2,0,1/4,1]

def IsDistanceMatrix {n : ℕ} (Γ : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ Γ i j) ∧ (∀ i j, Γ i j = Γ j i) ∧
  (∀ i, Γ i i = 0) ∧ (∀ i j k, Γ i k ≤ Γ i j + Γ j k)

noncomputable def lowerCount {B : ℕ} (ref : Fin B → ℝ) (obs : ℝ) : ℕ :=
  ∑ b, if ref b ≤ obs then 1 else 0

noncomputable def upperCount {B : ℕ} (ref : Fin B → ℝ) (obs : ℝ) : ℕ :=
  ∑ b, if obs ≤ ref b then 1 else 0

noncomputable def rawP {B : ℕ} (ref : Fin B → ℝ) (obs : ℝ) : ℝ :=
  doubledP ((lowerCount ref obs : ℝ)/B) ((upperCount ref obs : ℝ)/B)

abbrev Balanced (n m : ℕ) := {z : Assignment n // groupSize z true = m}

noncomputable def uniformMass (Ω : Type) [Fintype Ω] (E : Ω → Prop) : ℝ := by
  classical
  exact (∑ ω, if E ω then (1 : ℝ) else 0) / Fintype.card Ω

def EffectIncreasing {n : ℕ} (T : Outcome n → Assignment n → ℝ) : Prop :=
  ∀ z y y', (∀ i, if z i then y i ≤ y' i else y' i ≤ y i) → T y z ≤ T y' z

end SAP.P016a
