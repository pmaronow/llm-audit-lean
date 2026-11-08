import Mathlib
import SAP.P016a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016a
open scoped BigOperators
open Finset

def T9Statement : Prop :=
  ((∀ i : Fin 4, ecdf u4 (complete4 5) true (u4 i) - ecdf u4 (complete4 5) false (u4 i) =
      (![-1/2,-1,-1/2,0] : Outcome 4) i) ∧
    signedKS u4 (complete4 5) = 0 ∧ ks u4 (complete4 5) = 1 ∧
    signedKS u4 (complete4 0) = 1 ∧ ks u4 (complete4 0) = 1)
  ∧ (tss u4 = 5 ∧
    lowerP (uniformLaw (Fin 6)) (fun _ => tss u4) 0 = 1 ∧
    upperP (uniformLaw (Fin 6)) (fun _ => tss u4) 0 = 1 ∧
    lowerP (uniformLaw (Fin 6)) (fun k => rss u4 (complete4 k)) 0 = 1/3)
  ∧ (let S : Fin 6 → Fin 6 → ℝ := fun i j => if (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) then 1 else 0
    let z : Assignment 6 := ![true,false,true,false,true,false]
    let u : Outcome 6 := fun _ => 1
    let X := networkX S z
    let W := fun i : Fin 6 => (![bit (z i),treatedNeighbors S z i,degree S i] : Fin 3 → ℝ)
    (∀ i j, X i j = (!![1,1,0,1; 1,0,1,1; 1,1,0,0; 1,0,0,0; 1,1,0,0; 1,0,0,0] :
      Matrix (Fin 6) (Fin 4) ℝ) i j) ∧
    lsObjective u X ![1,0,0,0] = 0 ∧ lsRSS u X = 0 ∧
    lsObjective u W ![1,1,0] = 2 ∧ lsRSS u W = 2)
  ∧ (∀ k : Fin 6, rss u4 (complete4 k) = (![1,4,5,5,4,1] : Fin 6 → ℝ) k)
  ∧ (∀ {n : ℕ} (hn : 0 < n) {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (u : Outcome n) (assign : Ω → Assignment n) (z : Ω),
    (∀ ω, (fun _ : Assignment n => tss u) (assign ω) = tss u) ∧
    mass P (fun ω => (fun _ : Assignment n => tss u) (assign ω) = tss u) = 1 ∧
    lowerP P (fun _ => tss u) z = 1 ∧ upperP P (fun _ => tss u) z = 1)

def T10Statement : Prop :=
  (∀ {n : ℕ} (hn : 2 ≤ n) (u : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true),
    lsRSS u (basicX z) = rss u z ∧
    (∀ a b : ℝ, lsObjective u (basicX z) ![a,b] = rss u z ↔
      a = groupMean u z false ∧ b = meanDifference u z) ∧
    rss u z = (∑ i, (u i)^2) - (groupSize z false : ℝ)*(groupMean u z false)^2 -
      (groupSize z true : ℝ)*(groupMean u z true)^2)
  ∧ (∀ {n k : ℕ} (u : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true)
    (X : Fin n → Fin k → ℝ),
    (∃ b, lsObjective u X b = lsRSS u X) ∧
    (∀ b c, lsObjective u X b = lsRSS u X → lsObjective u X c = lsRSS u X → fitted X b = fitted X c))
  ∧ (∀ {n : ℕ} (u : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true),
    ks u z = sSup (Set.range (fun t : ℝ => |ecdf u z true t - ecdf u z false t|)) ∧
    ks u z = ks u (fun i => !(z i)) ∧ 0 ≤ ks u z ∧ ks u z ≤ 1)
  ∧ (∀ {n : ℕ} (S : Fin n → Fin n → ℝ)
    (hS : ∀ i j, S i j = S j i)
    (hbin : ∀ i j, S i j = 0 ∨ S i j = 1)
    (z : Assignment n)
    (h0 : 0 < groupSize z false)
    (h1 : 0 < groupSize z true)
    (i : Fin n),
    treatedNeighbors S z i =
      (∑ j, S i j * bit (z j)) ∧
    degree S i = (∑ j, S i j))

def T11Statement : Prop :=
  ((∀ i : Fin 4, if complete4 0 i then u4 i ≤ (![2,3,2,3] : Outcome 4) i
      else (![2,3,2,3] : Outcome 4) i ≤ u4 i) ∧
    ks u4 (complete4 0) = 1 ∧ ks ![2,3,2,3] (complete4 0) = 0 ∧
    signedKS u4 (complete4 0) = 1 ∧ signedKS ![2,3,2,3] (complete4 0) = 0 ∧
    (∀ i : Fin 4, if complete4 0 i then (![0,1,4,5] : Outcome 4) i < (![2,3,2,3] : Outcome 4) i
      else (![2,3,2,3] : Outcome 4) i < (![0,1,4,5] : Outcome 4) i) ∧
    ks ![0,1,4,5] (complete4 0) = 1)
  ∧ (rss ![0,2,0,2] (complete4 0) = 4 ∧
    rss ![1,2,0,2] (complete4 0) = 5/2 ∧
    rss ![0,3,0,2] (complete4 0) = 13/2 ∧
    (∀ i : Fin 4, (![0,2,0,2] : Outcome 4) i ≤ (![1,2,0,2] : Outcome 4) i ∧
      (![0,2,0,2] : Outcome 4) i ≤ (![0,3,0,2] : Outcome 4) i))
  ∧ (∀ i : Fin 4, ecdf u4 (complete4 0) true (u4 i) - ecdf u4 (complete4 0) false (u4 i) =
    (![1/2,1,1/2,0] : Outcome 4) i)
  ∧ (¬ EffectIncreasing (ks (n := 4)) ∧ ¬ EffectIncreasing (signedKS (n := 4)) ∧
    ¬ EffectIncreasing (rss (n := 4)) ∧ ¬ EffectIncreasing (fun u z => -rss (n := 4) u z))

end SAP.P016a
