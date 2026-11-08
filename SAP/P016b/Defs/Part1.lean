import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b
open scoped BigOperators
noncomputable section

abbrev Outcome (n : ℕ) := Fin n → ℝ
abbrev Assignment (n : ℕ) := Fin n → Bool

def bit (b : Bool) : ℝ := if b then 1 else 0

def groupSize {n : ℕ} (z : Assignment n) (g : Bool) : ℕ :=
  ∑ i, if z i = g then 1 else 0

def groupSum {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) : ℝ :=
  ∑ i, if z i = g then u i else 0

def groupMean {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) : ℝ :=
  groupSum u z g / groupSize z g

def pooledMean {n : ℕ} (u : Outcome n) : ℝ := (∑ i, u i) / n

def tss {n : ℕ} (u : Outcome n) : ℝ := ∑ i, (u i - pooledMean u)^2

/-- Residual sum of squares for the intercept-and-treatment regression. -/
def rss {n : ℕ} (u : Outcome n) (z : Assignment n) : ℝ :=
  ∑ i, (u i - groupMean u z (z i))^2

def meanDifference {n : ℕ} (u : Outcome n) (z : Assignment n) : ℝ :=
  groupMean u z true - groupMean u z false

def ecdf {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) (t : ℝ) : ℝ :=
  (∑ i, if z i = g ∧ u i ≤ t then (1 : ℝ) else 0) / groupSize z g

def sampleECDF {n : ℕ} (u : Outcome n) (t : ℝ) : ℝ :=
  (∑ i, if u i ≤ t then (1 : ℝ) else 0) / n

def ks {n : ℕ} (u : Outcome n) (z : Assignment n) : ℝ :=
  (List.ofFn fun i => |ecdf u z true (u i) - ecdf u z false (u i)|).foldr max 0

def signedKS {n : ℕ} (u : Outcome n) (z : Assignment n) : ℝ :=
  (List.ofFn fun i => ecdf u z true (u i) - ecdf u z false (u i)).foldr max 0

def additiveAdjust {n : ℕ} (Y : Outcome n) (Z : Assignment n) (t : ℝ) : Outcome n :=
  fun i => Y i - bit (Z i) * t

def additiveGenerate {n : ℕ} (y : Outcome n) (z : Assignment n) (t : ℝ) : Outcome n :=
  fun i => y i + bit (z i) * t

def multiplicativeAdjust {n : ℕ} (Y : Outcome n) (Z : Assignment n) (a : ℝ) : Outcome n :=
  fun i => Y i / (1 + bit (Z i) * (a - 1))

def multiplicativeGenerate {n : ℕ} (y : Outcome n) (z : Assignment n) (a : ℝ) : Outcome n :=
  fun i => y i * (1 + bit (z i) * (a - 1))

abbrev Balanced (n m : ℕ) := {z : Assignment n // groupSize z true = m}

def complete4 : Fin 6 → Assignment 4 :=
  ![![true,true,false,false], ![true,false,true,false], ![true,false,false,true],
    ![false,true,true,false], ![false,true,false,true], ![false,false,true,true]]

def u4 : Outcome 4 := ![0,1,2,3]

def EffectIncreasing {n : ℕ} (T : Outcome n → Assignment n → ℝ) : Prop :=
  ∀ z y y', (∀ i, if z i then y i ≤ y' i else y' i ≤ y i) → T y z ≤ T y' z

def EffectIncreasingOnGroups {n : ℕ} (T : Outcome n → Assignment n → ℝ) : Prop :=
  ∀ z, 0 < groupSize z false → 0 < groupSize z true → ∀ y y',
    (∀ i, if z i then y i ≤ y' i else y' i ≤ y i) → T y z ≤ T y' z

/-- Average of the two central order statistics; claims require a positive half-size. -/
def evenMedian {m : ℕ} (v : Outcome (2*m)) : ℝ :=
  let ordered := (List.ofFn v).mergeSort (fun a b => decide (a ≤ b))
  (ordered.getD (m-1) 0 + ordered.getD m 0)/2

def discrepancy {n : ℕ} (y : Outcome n) (z : Assignment n) (t a : ℝ) : Outcome n :=
  fun i => |multiplicativeGenerate y z a i - additiveGenerate y z t i|

def calibrationZ : Assignment 256 := fun i => decide (128 ≤ i.val)

/-- Constructed calibration witness, rather than the paper's simulation data. -/
def calibrationY : Outcome 256 := fun i =>
  if i.val < 64 then 9 else if i.val < 128 then 11 else if i.val = 128 then 8
  else if i.val < 192 then 9 else if i.val < 255 then 11 else 12

def treatedNeighbors {n : ℕ} (S : Fin n → Fin n → ℝ)
    (z : Assignment n) (i : Fin n) : ℝ := ∑ j, bit (z j) * S j i

def modelMultiplier {n : ℕ} (S : Fin n → Fin n → ℝ) (β τ : ℝ)
    (v : Assignment n) (i : Fin n) : ℝ :=
  β+(1-bit (v i))*(1-β)*Real.exp (-(τ^2)*treatedNeighbors S v i)

def modelMap {n : ℕ} (S : Fin n → Fin n → ℝ) (β τ : ℝ)
    (y : Outcome n) (z w : Assignment n) : Outcome n :=
  fun i => modelMultiplier S β τ w i / modelMultiplier S β τ z i * y i

end
end SAP.P016b
