import Mathlib
import SAP.P016a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016a
open scoped BigOperators
open Finset

def T3Statement : Prop :=
  ((∀ i j : Fin 4, similarity (fun k => some (scores4 k)) i j =
      (!![0,3/4,1/4,0; 3/4,0,1/2,1/4; 1/4,1/2,0,3/4; 0,1/4,3/4,0] :
        Matrix (Fin 4) (Fin 4) ℝ) i j) ∧
    (∀ i : Fin 4, conditionalMean (similarity (fun k => some (scores4 k))) matchedBank4 i false =
      (![7/8,9/8,9/8,7/8] : Outcome 4) i ∧
      conditionalMean (similarity (fun k => some (scores4 k))) matchedBank4 i true =
      (![1/8,3/8,3/8,1/8] : Outcome 4) i) ∧
    (∀ i : Fin 4, exposureSum (similarity (fun k => some (scores4 k))) (complete4 1) i =
      (![1/4,5/4,1/4,3/4] : Outcome 4) i ∧
      exposureSum (distance scores4) (complete4 1) i = (![3/2,3/2,3/2,5/2] : Outcome 4) i ∧
      centeredExposure (similarity (fun k => some (scores4 k))) matchedBank4 (complete4 1) i =
        (![1/8,1/8,-1/8,-1/8] : Outcome 4) i) ∧
    (¬ ∃ A B C : ℝ, ∀ i : Fin 4, (![1/8,1/8,-1/8,-1/8] : Outcome 4) i =
      A+B*bit (complete4 1 i)+C*(![1/4,5/4,1/4,3/4] : Outcome 4) i) ∧
    (¬ ∃ A B C : ℝ, ∀ i : Fin 4, (![1/8,1/8,-1/8,-1/8] : Outcome 4) i =
      A+B*bit (complete4 1 i)+C*(![3/2,3/2,3/2,5/2] : Outcome 4) i))
  ∧ (let S := similarity (fun k => some (scores6 k))
    let z : Assignment 6 := ![true,false,true,false,true,false]
    let h := centeredExposure S matchedBank6 z
    let x := exposureSum S z
    let y : Outcome 6 := ![0,1,0,1,1,0]
    (∀ i j : Fin 6, S i j =
      (!![0,7,6,4,3,0; 7,0,7,5,4,1; 6,7,0,6,5,2;
        4,5,6,0,7,4; 3,4,5,7,0,5; 0,1,2,4,5,0] : Matrix (Fin 6) (Fin 6) ℝ) i j/8) ∧
    (∀ i, x i = (![9/8,9/4,11/8,17/8,1,7/8] : Outcome 6) i ∧
      conditionalMean S matchedBank6 i (z i) = (![13/16,31/16,5/4,2,19/16,17/16] : Outcome 6) i ∧
      h i = (![5/16,5/16,1/8,1/8,-3/16,-3/16] : Outcome 6) i ∧
      degree S i = (![5/2,3,13/4,13/4,3,3/2] : Outcome 6) i) ∧
    pooledMean h = 1/12 ∧ sampleVariance h = 49/960 ∧
    (∀ i, standardize h i = Real.sqrt 15/42 * (![11,11,2,2,-13,-13] : Outcome 6) i) ∧
    (¬ ∃ A C : ℝ, ∀ i, h i = A+C*x i) ∧
    (¬ ∃ A B C : ℝ, ∀ i, h i = A+B*bit (z i)+C*x i) ∧
    lsRSS y (applicationX z h) = 4/3 ∧ lsRSS y (applicationX z (standardize h)) = 4/3 ∧
    lsRSS y (applicationX z x) = 655/708 ∧
    lsRSS y (fun i => (![1,bit (z i),x i,degree S i] : Fin 4 → ℝ)) = 515/859)
  ∧ (Matrix.det (!![1,1,1/4,1/8; 1,0,5/4,1/8; 1,1,1/4,-1/8; 1,0,3/4,-1/8] :
      Matrix (Fin 4) (Fin 4) ℝ) = 1/8 ∧
    Matrix.det (!![1,0,216630956840236/10000000000000,370753999962044/1000000000000000;
      1,0,191947426509578/10000000000000,240866262449021/1000000000000000;
      1,1,208676713418681/10000000000000,286925998351727/1000000000000000;
      1,1,225467332911212/10000000000000,-193126413625389/1000000000000000] :
      Matrix (Fin 4) (Fin 4) ℝ) = -14030283848669586515272953541/10^28)
  ∧ (¬ ∃ A B C : ℝ, ∀ i : Fin 4,
      (![370753999962044/10^15,240866262449021/10^15,
        286925998351727/10^15,-193126413625389/10^15] : Outcome 4) i =
      A+B*(![0,0,1,1] : Outcome 4) i + C*
        (![216630956840236/10^13,191947426509578/10^13,
          208676713418681/10^13,225467332911212/10^13] : Outcome 4) i)
  ∧ (let ref : Fin 1000 → ℝ := fun b => (b.val : ℝ)+1
    (lowerCount ref 25 = 25 ∧ upperCount ref 25 = 976 ∧ rawP ref 25 = 1/20 ∧
      codedReject (rawP ref 25) ∧ ¬ printedReject (rawP ref 25)) ∧
    (lowerCount ref 40 = 40 ∧ rawP ref 40 = 2/25 ∧
      (lowerCount ref 40 : ℝ)/1000 ≤ 1/20 ∧ ¬ codedReject (rawP ref 40)) ∧
    (lowerCount ref 980 = 980 ∧ rawP ref 980 = 21/500 ∧
      ¬ (lowerCount ref 980 : ℝ)/1000 ≤ 1/20 ∧ codedReject (rawP ref 980)))

def T4Statement : Prop :=
  (∀ {n N : ℕ} (hn : 2 ≤ n)
    (S : Fin n → Fin n → ℝ) (hS : ∀ i j, S i j = S j i) (hdiag : ∀ i, S i i = 0)
    (bank : Fin N → Assignment n) (hbank : ∀ i a, ∃ b, bank b i = a)
    (Ω : Finset (Assignment n)) (hsd : ∀ z ∈ Ω, 0 < sampleSD (centeredExposure S bank z))
    (y0 : Outcome n) (y : Assignment n → Outcome n) (b1 b2 : ℝ)
    (hmodel : ∀ z ∈ Ω, ∀ i, y z i = y0 i+bit (z i)*b1+b2*codedExposure S bank z i),
    ∀ z ∈ Ω, applicationAdjust (y z) z (codedExposure S bank z) b1 b2 = y0)
  ∧ (∀ {n : ℕ} (hn : 2 ≤ n) (h u : Outcome n) (z : Assignment n)
    (hs : 0 < sampleSD h),
    (∑ i, standardize h i) = 0 ∧ (∑ i, (standardize h i)^2)/((n : ℝ)-1) = 1 ∧
    lsRSS u (applicationX z (standardize h)) = lsRSS u (applicationX z h))
  ∧ (∀ {n N : ℕ} (hn : 2 ≤ n) (s : Outcome n)
    (bank : Fin N → Assignment n) (hbank : ∀ i a, ∃ b, bank b i = a)
    (z : Assignment n) (m : ℕ) (hz : groupSize z true = m)
    (hm : ∀ b, groupSize (bank b) true = m),
    let S := similarity (fun i => some (s i))
    let D := distance s
    (∀ i, exposureSum S z i = (m : ℝ)-bit (z i)-(1/2)*exposureSum D z i) ∧
    (∀ i, centeredExposure S bank z i = -(1/2)*centeredExposure D bank z i) ∧
    (0 < sampleSD (centeredExposure D bank z) →
      0 < sampleSD (centeredExposure S bank z) →
      codedExposure S bank z = fun i => -codedExposure D bank z i))
  ∧ (let S := similarity (fun k => some (scores4 k))
    let h := centeredExposure S matchedBank4 (complete4 1)
    0 < sampleSD h ∧
    (¬ ∃ A B C : ℝ, ∀ i, h i = A+B*bit (complete4 1 i)+C*exposureSum S (complete4 1) i) ∧
    (¬ ∃ A B C : ℝ, ∀ i, standardize h i = A+B*bit (complete4 1 i)+C*exposureSum S (complete4 1) i))
  ∧ (∀ {B : ℕ} (hB : 0 < B) (ref : Fin B → ℝ) (obs : ℝ),
    (lowerCount ref obs : ℝ)/B + (upperCount ref obs : ℝ)/B ≥ 1)
  ∧ (∀ (p α : ℝ),
    (p ≤ α ∧ ¬ p < α) ↔ p = α)
  ∧ (T3Statement)

end SAP.P016a
