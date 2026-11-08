import Mathlib
import SAP.P016a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016a
open scoped BigOperators
open Finset

def T1Statement : Prop :=
  (Function.Injective complete4 ∧
    ∀ z : Assignment 4, groupSize z true = 2 ↔ ∃ k, complete4 k = z)
  ∧ (Function.Injective blocked4 ∧
    ∀ z : Assignment 4, (z 0 ≠ z 2 ∧ z 1 ≠ z 3) ↔ ∃ k, blocked4 k = z)
  ∧ (pairedCovariance2 ![0,2] ![1,3] = 1 ∧
    pairedCovariance2 ![0,2] ![3,1] = -1 ∧
    rss ![0,2,1,3] (complete4 0) = 4 ∧ rss ![0,2,3,1] (complete4 0) = 4 ∧
    ks ![0,2,1,3] (complete4 0) = 1/2 ∧ ks ![0,2,3,1] (complete4 0) = 1/2)
  ∧ ((∀ k, rss u4 (complete4 k) = (![1,4,5,5,4,1] : Fin 6 → ℝ) k ∧
      ks u4 (complete4 k) = (![1,1/2,1/2,1/2,1/2,1] : Fin 6 → ℝ) k) ∧
    (∀ k, rss u4 (blocked4 k) = (![1,5,5,1] : Fin 4 → ℝ) k ∧
      ks u4 (blocked4 k) = (![1,1/2,1/2,1] : Fin 4 → ℝ) k))
  ∧ (mass (uniformLaw (Fin 6)) (fun k => rss u4 (complete4 k) ≤ rss u4 (complete4 0)) = 1/3 ∧
    mass (uniformLaw (Fin 6)) (fun k => ks u4 (complete4 0) ≤ ks u4 (complete4 k)) = 1/3 ∧
    covariance (uniformLaw (Fin 6)) (fun k => groupMean u4 (complete4 k) true)
      (fun k => groupMean u4 (complete4 k) false) = -5/12 ∧
    mass (uniformLaw (Fin 4)) (fun k => rss u4 (blocked4 k) ≤ rss u4 (blocked4 0)) = 1/2 ∧
    mass (uniformLaw (Fin 4)) (fun k => ks u4 (blocked4 0) ≤ ks u4 (blocked4 k)) = 1/2 ∧
    covariance (uniformLaw (Fin 4)) (fun k => groupMean u4 (blocked4 k) true)
      (fun k => groupMean u4 (blocked4 k) false) = -1/2)

def T2Statement : Prop :=
  (∀ {n : ℕ} (hn : 2 ≤ n) (u : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true),
    lsRSS u (basicX z) = rss u z ∧
    (∀ a b : ℝ, lsObjective u (basicX z) ![a,b] = rss u z ↔
      a = groupMean u z false ∧ b = meanDifference u z) ∧
    rss u z = (∑ i, (u i)^2) - (groupSize z false : ℝ)*(groupMean u z false)^2 -
      (groupSize z true : ℝ)*(groupMean u z true)^2)
  ∧ (∀ {n : ℕ} (hn : 2 ≤ n) (u : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true),
    rss u z = tss u - (groupSize z false : ℝ)*groupSize z true/n*(meanDifference u z)^2)
  ∧ (∀ {n : ℕ} (hn : 2 ≤ n) (u : Outcome n) (z w : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true)
    (hw : groupSize w true = groupSize z true),
    rss u w ≤ rss u z ↔ |meanDifference u z| ≤ |meanDifference u w|)
  ∧ (∀ {n : ℕ} {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (hn : 2 ≤ n) (u : Outcome n) (zobs : Assignment n) (assign : Ω → Assignment n)
    (h0 : 0 < groupSize zobs false) (h1 : 0 < groupSize zobs true)
    (hsize : ∀ ω, groupSize (assign ω) true = groupSize zobs true),
    mass P (fun ω => rss u (assign ω) ≤ rss u zobs) =
      mass P (fun ω => |meanDifference u zobs| ≤ |meanDifference u (assign ω)|))
  ∧ (∀ {n : ℕ} (hn : 2 ≤ n) (u : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true),
    rss u z = (groupSize z false : ℝ) * (groupMean (fun i => (u i)^2) z false -
      (groupMean u z false)^2) + (groupSize z true : ℝ) *
      (groupMean (fun i => (u i)^2) z true - (groupMean u z true)^2))
  ∧ (∀ {n : ℕ} (hn : 2 ≤ n) (u v : Outcome n) (z w : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true) (hm : sameMargins u z v w),
    rss u z = rss v w ∧ ks u z = ks v w)
  ∧ (∀ {n : ℕ} {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (hn : 2 ≤ n) (u : Outcome n) (assign : Ω → Assignment n) (n0 n1 : ℕ)
    (h0 : 0 < n0) (h1 : 0 < n1)
    (hsize : ∀ ω, groupSize (assign ω) false = n0 ∧ groupSize (assign ω) true = n1),
    (∀ ω, (n1 : ℝ)*groupMean u (assign ω) true + (n0 : ℝ)*groupMean u (assign ω) false =
      n*pooledMean u) ∧
    covariance P (fun ω => groupMean u (assign ω) true) (fun ω => groupMean u (assign ω) false) =
      -(n1 : ℝ)/n0 * variance P (fun ω => groupMean u (assign ω) true) ∧
    (∀ x : ℝ, (∀ ω, (n1 : ℝ)*ecdf u (assign ω) true x + (n0 : ℝ)*ecdf u (assign ω) false x =
      ∑ i, if u i ≤ x then (1 : ℝ) else 0) ∧
      covariance P (fun ω => ecdf u (assign ω) true x) (fun ω => ecdf u (assign ω) false x) =
        -(n1 : ℝ)/n0 * variance P (fun ω => ecdf u (assign ω) true x)))
  ∧ (let z := complete4 1
    let S : Fin 4 → Fin 4 → ℝ := !![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,1,0]
    let X := fun i : Fin 4 => (![1,bit (z i),degree S i] : Fin 3 → ℝ)
    sameMargins u4 z ![2,1,0,3] z ∧
    rss u4 z = 4 ∧ rss ![2,1,0,3] z = 4 ∧ ks u4 z = 1/2 ∧ ks ![2,1,0,3] z = 1/2 ∧
    (∀ i, degree S i = (![1,1,2,2] : Outcome 4) i) ∧
    lsObjective u4 X ![-1,-1,2] = 0 ∧ lsRSS u4 X = 0 ∧
    lsObjective ![2,1,0,3] X ![2,-1,0] = 4 ∧ lsRSS ![2,1,0,3] X = 4)
  ∧ (ks u4 (complete4 1) = 1/2 ∧ ks u4 (complete4 2) = 1/2 ∧
    rss u4 (complete4 1) = 4 ∧ rss u4 (complete4 2) = 5)
  ∧ (∀ {n : ℕ} (u : Outcome n) (z : Assignment n),
    0 < groupSize z false → 0 < groupSize z true →
    rss u z = groupSum (fun i => (u i-groupMean u z false)^2) z false +
      groupSum (fun i => (u i-groupMean u z true)^2) z true)
  ∧ (∀ {n : ℕ} (u : Outcome n) (z : Assignment n),
    0 < groupSize z false → 0 < groupSize z true →
      ∃ b, lsObjective u (basicX z) b = lsRSS u (basicX z))

end SAP.P016a
