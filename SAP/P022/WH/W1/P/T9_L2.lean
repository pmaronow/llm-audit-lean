import SAP.P022.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T9_L2

open SAP.P022
open scoped BigOperators

theorem finiteMean_translate {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (c : ℝ) :
    finiteMean (fun i => a i + c) = finiteMean a + c := by
  classical
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold finiteMean
  rw [Finset.expect_add_distrib]
  simp

theorem sortedOutcomes_translate {n : ℕ} (a : Fin n → ℝ) (c : ℝ) :
    sortedOutcomes (fun i => a i + c) = (sortedOutcomes a).map (fun x => x + c) := by
  classical
  have hmap : List.ofFn (fun i : Fin n => a i + c) =
      (List.ofFn a).map (fun x => x + c) := by
    calc
      List.ofFn (fun i : Fin n => a i + c) =
          List.ofFn ((fun x => x + c) ∘ a) := by rfl
      _ = (List.ofFn a).map (fun x => x + c) :=
        (List.map_ofFn (f := a) (g := fun x => x + c)).symm
  have hperm : List.Perm
      ((List.ofFn (fun i : Fin n => a i + c)).mergeSort (fun x y => decide (x ≤ y)))
      (((List.ofFn a).mergeSort (fun x y => decide (x ≤ y))).map (fun x => x + c)) := by
    rw [hmap]
    exact List.Perm.trans (List.mergeSort_perm _ _)
      ((List.Perm.map (fun x => x + c) (List.mergeSort_perm _ _)).symm)
  have hsort₁ :
      ((List.ofFn (fun i : Fin n => a i + c)).mergeSort (fun x y => decide (x ≤ y))).SortedLE := by
    exact List.sortedLE_mergeSort
  have hsortA : ((List.ofFn a).mergeSort (fun x y => decide (x ≤ y))).SortedLE := by
    exact List.sortedLE_mergeSort
  have hsort₂ :
      (((List.ofFn a).mergeSort (fun x y => decide (x ≤ y))).map (fun x => x + c)).SortedLE := by
    rw [List.sortedLE_iff_pairwise] at hsortA ⊢
    rw [List.pairwise_map]
    exact hsortA.imp (by intro x y hxy; nlinarith [hxy])
  exact List.Perm.eq_of_sortedLE hsort₁ hsort₂ hperm

theorem orderStatistic_translate {n : ℕ} (a : Fin n → ℝ) (c : ℝ)
    {r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) :
    orderStatistic (fun i => a i + c) r = orderStatistic a r + c := by
  have hsort := sortedOutcomes_translate a c
  have hlen : (sortedOutcomes a).length = n := by simp [sortedOutcomes]
  have hi : r - 1 < (sortedOutcomes a).length := by rw [hlen]; omega
  have hi' : r - 1 < ((sortedOutcomes a).map (fun x => x + c)).length := by
    simpa using hi
  unfold orderStatistic
  rw [hsort]
  have hgm := List.getD_map (sortedOutcomes a) (-c) (n := r - 1) (fun x => x + c)
  have hdefault : (sortedOutcomes a).getD (r - 1) (-c) =
      (sortedOutcomes a).getD (r - 1) 0 := by
    rw [List.getD_eq_getElem (sortedOutcomes a) (-c) hi,
      List.getD_eq_getElem (sortedOutcomes a) 0 hi]
  calc
    _ = (sortedOutcomes a).getD (r - 1) (-c) + c := by
      simpa only [neg_add_cancel] using hgm
    _ = (sortedOutcomes a).getD (r - 1) 0 + c := by rw [hdefault]

theorem sampleVariance_translate {n : ℕ} (hn : 1 < n) (a : Fin n → ℝ) (c : ℝ) :
    sampleVariance (fun i => a i + c) = sampleVariance a := by
  classical
  unfold sampleVariance
  rw [finiteMean_translate (by omega) a c]
  have hterms :
      (fun i : Fin n => (a i + c - (finiteMean a + c)) ^ 2) =
        fun i => (a i - finiteMean a) ^ 2 := by
    funext i
    congr 1
    ring
  rw [hterms]

theorem sharpCovariance_translate {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (c : ℝ) (B : BoundSide) :
    sharpCovariance (fun i => a i + c) (fun j => b j + c) B = sharpCovariance a b B := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, hrep⟩ :=
    Bridge.appendixB_corrected_proof hm hk a b
  obtain ⟨_, _, _, _, _, _, _, _, hrepShift⟩ :=
    Bridge.appendixB_corrected_proof hm hk (fun i => a i + c) (fun j => b j + c)
  rw [hrepShift B, hrep B]
  rw [finiteMean_translate (by omega) a c, finiteMean_translate (by omega) b c]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hri : 1 ≤ i.val + 1 := by omega
  have hri' : i.val + 1 ≤ m := by omega
  have hrj : 1 ≤ (if B = BoundSide.H then j.val + 1 else k - j.val) := by
    by_cases hB : B = BoundSide.H
    · simp [hB]
    · simp [hB]
      omega
  have hrj' : (if B = BoundSide.H then j.val + 1 else k - j.val) ≤ k := by
    by_cases hB : B = BoundSide.H
    · simp [hB]
    · simp [hB]
  rw [orderStatistic_translate a c hri hri',
    orderStatistic_translate b c hrj hrj']
  ring

theorem sampleBound_translate {N m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (c : ℝ) (B : BoundSide) :
    estimateBound N (fun i => a i + c) (fun j => b j + c) B = estimateBound N a b B := by
  unfold estimateBound marginalVarianceEstimate
  rw [sampleVariance_translate (by omega) a c,
    sampleVariance_translate (by omega) b c,
    sharpCovariance_translate hm hk a b c B]

end SAP.P022.WH.W1.P.T9_L2

theorem SAP.P022.WH.W1.T9_L2_proof : SAP.P022.WH.W1.T9_L2 := by
  constructor
  · intro N m k hm hk hN a b c B
    exact SAP.P022.WH.W1.P.T9_L2.sampleBound_translate hm hk a b c B
  · intro n hn a c r hr hrn
    exact SAP.P022.WH.W1.P.T9_L2.orderStatistic_translate a c hr hrn
