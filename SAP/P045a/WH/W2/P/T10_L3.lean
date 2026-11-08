import SAP.P045a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a.WH.W2.P.T10_L3

open SAP.P045a.Bridge
open AronowAudit.P045

private theorem pair_toList (a : Fin 4) (ha : a ≠ 0) :
    ({0,a} : Finset (Fin 4)).toList = [0,a] ∨
    ({0,a} : Finset (Fin 4)).toList = [a,0] := by
  apply List.perm_pair.mp
  simpa only [Finset.toList_singleton] using
    (Finset.toList_insert (s := ({a} : Finset (Fin 4))) (by simpa using Ne.symm ha))

private theorem nearest_pairs (v : Fin 4) :
    nearestCentre pathDistance {0,1} v = some (if v = 0 then 0 else 1) ∧
    nearestCentre pathDistance {0,2} v = some (if v.val < 2 then 0 else 2) ∧
    nearestCentre pathDistance {0,3} v = some (if v.val < 2 then 0 else 3) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases pair_toList 1 (by decide) with h | h <;>
      rw [nearestCentre, h] <;> fin_cases v <;>
      simp +decide [List.mergeSort, List.MergeSort.Internal.splitInTwo]
  · rcases pair_toList 2 (by decide) with h | h <;>
      rw [nearestCentre, h] <;> fin_cases v <;>
      simp +decide [List.mergeSort, List.MergeSort.Internal.splitInTwo]
  · rcases pair_toList 3 (by decide) with h | h <;>
      rw [nearestCentre, h] <;> fin_cases v <;>
      simp +decide [List.mergeSort, List.MergeSort.Internal.splitInTwo]

private theorem nearest_single (a v : Fin 4) :
    nearestCentre pathDistance {a} v = some a := by
  simp [nearestCentre]

private theorem two_coins (i j : Fin 4) (hij : i ≠ j) (A B : Bool → Prop)
    [DecidablePred A] [DecidablePred B] :
    prob (bernoulli (1/2)) (fun c : Assignment 4 => A (c i) ∧ B (c j)) =
      ((if A true then (1/2 : ℝ) else 0) + (if A false then 1/2 else 0)) *
      ((if B true then (1/2 : ℝ) else 0) + (if B false then 1/2 else 0)) := by
  classical
  let q : Bool → ℝ := fun b => if b then 1/2 else 1 - 1/2
  let X : Bool → ℝ := fun b => if A b then 1 else 0
  let Y : Bool → ℝ := fun b => if B b then 1 else 0
  have hq : ∑ b, q b = 1 := by norm_num [q, Fintype.univ_bool]
  have hXY : prob (bernoulli (1/2)) (fun c : Assignment 4 => A (c i) ∧ B (c j)) =
      expect (bernoulli (1/2)) (fun c => X (c i) * Y (c j)) := by
    unfold prob
    congr 1
    funext c
    by_cases hA : A (c i) <;> by_cases hB : B (c j) <;> simp [X, Y, hA, hB]
  rw [hXY]
  change AronowAudit.P045.expect
      (fun c : Fin 4 → Bool => ∏ g, q (c g))
      (fun c => X (c i) * Y (c j)) = _
  rw [AronowAudit.P045.independent_pair_expect q hq i j hij X Y]
  norm_num [AronowAudit.P045.expect, q, X, Y, Fintype.univ_bool, mul_ite]

private theorem coin_single (a : Fin 4) (z : Assignment 4) :
    clusterProb pathDistance {a} (1/2) z =
      if z 0 = z 1 ∧ z 1 = z 2 ∧ z 2 = z 3 then 1/2 else 0 := by
  classical
  let F : Bool → ℝ := fun b => if ∀ v : Fin 4, z v = b then 1 else 0
  have h : clusterProb pathDistance {a} (1/2) z =
      expect (bernoulli (1/2)) (fun c : Assignment 4 => F (c a)) := by
    unfold clusterProb prob
    congr 1
    funext c
    simp [F, nearest_single]
  rw [h]
  change AronowAudit.P045.expect (AronowAudit.P045.bernoulli (1/2))
      (fun c : AronowAudit.P045.Assignment 4 => F (c a)) = _
  rw [AronowAudit.P045.bernoulli_coordinate_expect (n := 3)]
  cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;> cases h3 : z 3 <;>
    norm_num [F, Fin.forall_fin_succ, h0, h1, h2, h3]

private theorem coin_03 (z : Assignment 4) :
    clusterProb pathDistance {0,3} (1/2) z =
      if z 0 = z 1 ∧ z 2 = z 3 then 1/4 else 0 := by
  classical
  have he : (fun c : Assignment 4 => ∀ v, ∃ s,
      nearestCentre pathDistance {0,3} v = some s ∧ z v = c s) =
      (fun c => (z 0 = c 0 ∧ z 1 = c 0) ∧ (z 2 = c 3 ∧ z 3 = c 3)) := by
    funext c
    simp_rw [(nearest_pairs _).2.2]
    simp [Fin.forall_fin_succ, and_assoc]
  unfold clusterProb
  rw [he]
  have hcoin := two_coins 0 3 (by decide)
    (fun b => z 0 = b ∧ z 1 = b) (fun b => z 2 = b ∧ z 3 = b)
  rw [hcoin]
  cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;> cases h3 : z 3 <;>
    norm_num [h0, h1, h2, h3]

private theorem pair_equalities_mem (z : Assignment 4)
    (h01 : z 0 = z 1) (h23 : z 2 = z 3) : z ∈ fourPathRepairedVectors := by
  have hz : z = ![z 0, z 0, z 2, z 2] := by
    funext i
    fin_cases i <;> simp [h01, h23]
  rw [hz]
  cases h0 : z 0 <;> cases h2 : z 2 <;>
    simp [fourPathRepairedVectors]

end SAP.P045a.WH.W2.P.T10_L3

open SAP.P045a.WH.W2.P.T10_L3

theorem SAP.P045a.WH.W2.T10_L3_proof : SAP.P045a.WH.W2.T10_L3 := by
  classical
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold nearestPartition
      simp_rw [(nearest_pairs _).1]
      decide
    · unfold nearestPartition
      simp_rw [(nearest_pairs _).2.1]
      decide
    · unfold nearestPartition
      simp_rw [(nearest_pairs _).2.2]
      decide
    · unfold nearestPartition
      simp_rw [nearest_single]
      decide
    · unfold nearestPartition
      simp_rw [nearest_single]
      decide
  · intro z hz S hS
    have hpair : ¬ (z 0 = z 1 ∧ z 2 = z 3) := by
      intro hp
      exact hz (pair_equalities_mem z hp.1 hp.2)
    have hsingle : ¬ (z 0 = z 1 ∧ z 1 = z 2 ∧ z 2 = z 3) := by
      intro hp
      apply hpair
      exact ⟨hp.1, hp.2.2⟩
    simp only [fourPathRepairedCentreSets, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with hS | hS | hS
    · rw [hS, coin_03]
      simp [hpair]
    · rw [hS, coin_single]
      simp [hsingle]
    · rw [hS, coin_single]
      simp [hsingle]

