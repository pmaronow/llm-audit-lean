import SAP.P003b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P003b.WH.W2.P.T30_L1

open scoped BigOperators
open SAP.P003b

theorem card_bool_split {n : ℕ} (A : Finset (Fin n)) (Y : Fin n → Bool) :
    (A.filter fun i => Y i = true).card +
      (A.filter fun i => Y i = false).card = A.card := by
  classical
  have hn : A.filter (fun i => ¬ Y i = true) = A.filter (fun i => Y i = false) := by
    ext i
    simp
  rw [← hn]
  exact Finset.card_filter_add_card_filter_not (s := A) (fun i => Y i = true)

theorem observed_arm_sums {n : ℕ} (Y : Fin n → Bool) (z : Finset (Fin n)) :
    let o := wholeObservedCounts Y z
    o.a + o.b = z.card ∧ o.c + o.d = n - z.card := by
  classical
  dsimp
  let T : Finset (Fin n) := Finset.univ.filter fun i => i ∈ z
  let C : Finset (Fin n) := Finset.univ.filter fun i => i ∉ z
  have hT11 : (Finset.univ.filter fun i => i ∈ z ∧ Y i = true) =
      T.filter fun i => Y i = true := by
    ext i
    simp [T]
  have hT10 : (Finset.univ.filter fun i => i ∈ z ∧ Y i = false) =
      T.filter fun i => Y i = false := by
    ext i
    simp [T]
  have hC01 : (Finset.univ.filter fun i => i ∉ z ∧ Y i = true) =
      C.filter fun i => Y i = true := by
    ext i
    simp [C]
  have hC00 : (Finset.univ.filter fun i => i ∉ z ∧ Y i = false) =
      C.filter fun i => Y i = false := by
    ext i
    simp [C]
  have ht : T = z := by
    ext i
    simp [T]
  have hcomp : T.card + C.card = n := by
    have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i => i ∈ z)
    simpa [T, C] using hc
  constructor
  · change (Finset.univ.filter fun i => i ∈ z ∧ Y i = true).card +
      (Finset.univ.filter fun i => i ∈ z ∧ Y i = false).card = z.card
    rw [hT11, hT10]
    rw [ht]
    exact card_bool_split z Y
  · change (Finset.univ.filter fun i => i ∉ z ∧ Y i = true).card +
      (Finset.univ.filter fun i => i ∉ z ∧ Y i = false).card = n - z.card
    rw [hC01, hC00]
    have hcomp' : z.card + C.card = n := by simpa [ht] using hcomp
    calc
      (C.filter fun i => Y i = true).card + (C.filter fun i => Y i = false).card =
          C.card := card_bool_split C Y
      _ = n - z.card := by omega

theorem witness_counts {n : ℕ} (Y : Fin n → Bool) (z : Finset (Fin n)) :
    let o := wholeObservedCounts Y z
    let w := wholeBalancedWitness Y z
    tableCounts w = wholeBalancedVector o := by
  classical
  dsimp
  let N11 : Finset (Fin n) := Finset.univ.filter fun i => i ∈ z ∧ Y i = true
  let N10 : Finset (Fin n) := Finset.univ.filter fun i => i ∈ z ∧ Y i = false
  let N01 : Finset (Fin n) := Finset.univ.filter fun i => i ∉ z ∧ Y i = true
  let N00 : Finset (Fin n) := Finset.univ.filter fun i => i ∉ z ∧ Y i = false
  let w : PotentialTable n := wholeBalancedWitness Y z
  have h11 : (Finset.univ.filter fun i => w i = (true, true)) = ∅ := by
    ext i
    by_cases hz : i ∈ z <;> cases hy : Y i <;>
      simp [w, wholeBalancedWitness, hz, hy]
  have h00 : (Finset.univ.filter fun i => w i = (false, false)) = ∅ := by
    ext i
    by_cases hz : i ∈ z <;> cases hy : Y i <;>
      simp [w, wholeBalancedWitness, hz, hy]
  have h10 : (Finset.univ.filter fun i => w i = (true, false)) = N11 ∪ N00 := by
    ext i
    by_cases hz : i ∈ z <;> cases hy : Y i <;>
      simp [N11, N00, w, wholeBalancedWitness, hz, hy]
  have h01 : (Finset.univ.filter fun i => w i = (false, true)) = N10 ∪ N01 := by
    ext i
    by_cases hz : i ∈ z <;> cases hy : Y i <;>
      simp [N10, N01, w, wholeBalancedWitness, hz, hy]
  have hdisj11 : Disjoint N11 N00 := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [N11, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [N00, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj.1 hi.1
  have hdisj10 : Disjoint N10 N01 := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [N10, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [N01, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj.1 hi.1
  have hcard10 : (Finset.univ.filter fun i => w i = (true, false)).card =
      (wholeObservedCounts Y z).a + (wholeObservedCounts Y z).d := by
    rw [h10, Finset.card_union_of_disjoint hdisj11]
    simp [N11, N00, wholeObservedCounts]
  have hcard01 : (Finset.univ.filter fun i => w i = (false, true)).card =
      (wholeObservedCounts Y z).b + (wholeObservedCounts Y z).c := by
    rw [h01, Finset.card_union_of_disjoint hdisj10]
    simp [N10, N01, wholeObservedCounts]
  apply Counts.ext
  · change (Finset.univ.filter fun i => w i = (true, true)).card = 0
    rw [h11]
    simp
  · simpa [tableCounts, wholeBalancedVector, w] using hcard10
  · simpa [tableCounts, wholeBalancedVector, w] using hcard01
  · change (Finset.univ.filter fun i => w i = (false, false)).card = 0
    rw [h00]
    simp

theorem witness_agrees {n : ℕ} (Y : Fin n → Bool) (z : Finset (Fin n)) :
    wholeAgrees (wholeBalancedWitness Y z) Y z := by
  intro i
  by_cases hz : i ∈ z <;> simp [wholeBalancedWitness, hz]

theorem witness_success_sums {n : ℕ} (Y : Fin n → Bool) (z : Finset (Fin n)) :
    let w := wholeBalancedWitness Y z
    (∑ i : Fin n, if i ∈ z then bit (w i).1 else 0) =
      (wholeObservedCounts Y z).a ∧
    (∑ i : Fin n, if i ∈ z then 0 else bit (w i).2) =
      (wholeObservedCounts Y z).c := by
  classical
  dsimp
  constructor
  · calc
      (∑ i : Fin n, if i ∈ z then bit (wholeBalancedWitness Y z i).1 else 0) =
          ∑ i : Fin n, if i ∈ z ∧ Y i = true then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hiz : i ∈ z <;> cases hy : Y i <;>
              simp [wholeBalancedWitness, hiz, hy, bit]
      _ = ((Finset.univ.filter fun i => i ∈ z ∧ Y i = true).card : ℝ) := by
            simp only [Finset.sum_boole]
      _ = (wholeObservedCounts Y z).a := rfl
  · calc
      (∑ i : Fin n, if i ∈ z then 0 else bit (wholeBalancedWitness Y z i).2) =
          ∑ i : Fin n, if i ∉ z ∧ Y i = true then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hiz : i ∈ z <;> cases hy : Y i <;>
              simp [wholeBalancedWitness, hiz, hy, bit]
      _ = ((Finset.univ.filter fun i => i ∉ z ∧ Y i = true).card : ℝ) := by
            simp only [Finset.sum_boole]
      _ = (wholeObservedCounts Y z).c := rfl

end SAP.P003b.WH.W2.P.T30_L1

open scoped BigOperators
open SAP.P003b
open SAP.P003b.WH.W2.P.T30_L1

theorem SAP.P003b.WH.W2.T30_L1_proof : SAP.P003b.WH.W2.T30_L1 := by
  intro n Y z
  dsimp
  let o := wholeObservedCounts Y z
  let w := wholeBalancedWitness Y z
  have harms := observed_arm_sums Y z
  have hT : (wholeObservedCounts Y z).a + (wholeObservedCounts Y z).b = z.card := by
    simpa [o] using harms.1
  have hC : (wholeObservedCounts Y z).c + (wholeObservedCounts Y z).d = n - z.card := by
    simpa [o] using harms.2
  have htot : o.total = n := by
    have hsum : (wholeObservedCounts Y z).a + (wholeObservedCounts Y z).b +
        (wholeObservedCounts Y z).c + (wholeObservedCounts Y z).d = n := by
      have hzle : z.card ≤ n := by simpa using Finset.card_le_univ z
      omega
    simpa [o, Counts.total] using hsum
  have hagree : wholeAgrees w Y z := by
    simpa [w] using witness_agrees Y z
  have hcounts : tableCounts w = wholeBalancedVector o := by
    simpa [o, w] using witness_counts Y z
  refine ⟨htot, by simpa [o] using hT, by simpa [o] using hC, hagree, hcounts, ?_⟩
  intro hz hzn
  have hsuccess := witness_success_sums Y z
  dsimp [w, o] at hsuccess
  have hdenT : (z.card : ℝ) = (o.a : ℝ) + (o.b : ℝ) := by
    exact_mod_cast hT.symm
  have hdenC : ((n - z.card : ℕ) : ℝ) = (o.c : ℝ) + (o.d : ℝ) := by
    exact_mod_cast hC.symm
  have hnrem : n - ((wholeObservedCounts Y z).a + (wholeObservedCounts Y z).b) =
      (wholeObservedCounts Y z).c + (wholeObservedCounts Y z).d := by omega
  have hdenC' : (n : ℝ) - ((o.a : ℝ) + (o.b : ℝ)) =
      (o.c : ℝ) + (o.d : ℝ) := by
    dsimp [o]
    rw [← Nat.cast_add, ← Nat.cast_sub
      (show (wholeObservedCounts Y z).a + (wholeObservedCounts Y z).b ≤ n by omega)]
    exact_mod_cast hnrem
  rw [tableEstimator, hsuccess.1, hsuccess.2, hdenT, hdenC']
  simp [o, estimate, estimateQ, Rat.cast_sub, Rat.cast_div]

