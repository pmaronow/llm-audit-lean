import SAP.P045a.WH.W2.Leaves
import AronowAudit.P045.Wave1.ClusterSampler.N3
import AronowAudit.P045.Wave1.ClusterSampler.N5

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a.WH.W2.P.T10_L1

open SAP.P045a
noncomputable section

private theorem coded_classify : ∀ cs : List (Fin 4),
    traceMass pathDistance 3 true cs ≠ 0 →
      cs = [1] ∨ cs = [2] ∨ cs = [3, 0] ∨
        ∃ r : ℕ, ∃ j : Fin 4, j ≠ 0 ∧
          cs = List.replicate (r + 1) 0 ++ [j] :=
  AronowAudit.P045.Wave1.ClusterSampler.n5_proof
    AronowAudit.P045.Wave1.ClusterSampler.n3_proof

private theorem coded_off (S : Finset (Fin 4))
    (hS : S ∉ fourPathCodedCentreSets) :
    terminalCentres pathDistance 3 true S = 0 := by
  classical
  unfold terminalCentres
  calc
    (∑' t : ℕ, ∑ z : Fin t → Fin 4,
        if (List.ofFn z).toFinset = S then
          traceMass pathDistance 3 true (List.ofFn z) else 0) =
      ∑' _t : ℕ, (0 : ℝ) := by
        apply tsum_congr
        intro t
        apply Finset.sum_eq_zero
        intro z _
        by_cases hs : (List.ofFn z).toFinset = S
        · rw [if_pos hs]
          by_contra hm
          apply hS
          rcases coded_classify (List.ofFn z) hm with h | h | h | ⟨r, j, hj, h⟩
          · have hset : S = ({1} : Finset (Fin 4)) := by simpa [h] using hs.symm
            simp [fourPathCodedCentreSets, hset]
          · have hset : S = ({2} : Finset (Fin 4)) := by simpa [h] using hs.symm
            simp [fourPathCodedCentreSets, hset]
          · have hset : S = ({0, 3} : Finset (Fin 4)) := by
              simpa [h, Finset.pair_comm] using hs.symm
            simp [fourPathCodedCentreSets, hset]
          · have hset : S = ({0, j} : Finset (Fin 4)) := by
              simpa [h, List.toFinset_append,
                List.toFinset_replicate_of_ne_zero (by omega : r + 1 ≠ 0)] using hs.symm
            fin_cases j <;> simp_all [fourPathCodedCentreSets]
        · rw [if_neg hs]
    _ = 0 := tsum_zero

private theorem nonzero_data {cs : List (Fin 4)}
    (hm : traceMass pathDistance 3 false cs ≠ 0) :
    (∀ k : Fin cs.length,
      marked pathDistance 3 (cs.take k.val).toFinset ≠ univ) ∧
      marked pathDistance 3 cs.toFinset = univ := by
  classical
  by_contra ht
  exact hm (by simp only [traceMass, if_neg ht])

private theorem nonzero_draw {cs : List (Fin 4)}
    (hm : traceMass pathDistance 3 false cs ≠ 0) (k : Fin cs.length) :
    centreDraw pathDistance 3 false (cs.take k.val).toFinset (cs.get k) ≠ 0 := by
  classical
  have ht := nonzero_data hm
  have hp :
      (∏ i : Fin cs.length,
        centreDraw pathDistance 3 false (cs.take i.val).toFinset (cs.get i)) ≠ 0 := by
    simpa only [traceMass, if_pos ht] using hm
  intro hk
  exact hp (Finset.prod_eq_zero (Finset.mem_univ k) hk)

private theorem repaired_kernel_support (S : Finset (Fin 4)) (v : Fin 4)
    (hf : centreDraw pathDistance 3 false S v ≠ 0) :
    centreDraw pathDistance 3 true S v ≠ 0 := by
  classical
  let R := (univ : Finset (Fin 4)) \ marked pathDistance 3 S
  simp only [centreDraw, Bool.false_eq_true, false_and, ↓reduceIte] at hf
  change (if v ∈ R then 1 / (R.card : ℝ) else 0) ≠ 0 at hf
  change (if true = true ∧ R.card = 1 then
      let u := R.toList.head?.getD v
      if v.val ≤ u.val then (1 : ℝ) / (u.val + 1 : ℕ) else 0
    else if v ∈ R then 1 / (R.card : ℝ) else 0) ≠ 0
  by_cases hc : R.card = 1
  · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hc
    have hv : v = u := by
      by_contra hv
      simp [hu, hv] at hf
    subst v
    simp [hu, Nat.cast_add, Nat.cast_one]
    positivity
  · simpa [hc] using hf

private theorem repaired_classify (cs : List (Fin 4))
    (hm : traceMass pathDistance 3 false cs ≠ 0) :
    cs = [1] ∨ cs = [2] ∨ cs = [3, 0] ∨ cs = [0, 3] := by
  classical
  have ht := nonzero_data hm
  have hcode : traceMass pathDistance 3 true cs ≠ 0 := by
    rw [traceMass, if_pos ht]
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact repaired_kernel_support _ _ (nonzero_draw hm k)
  rcases coded_classify cs hcode with h | h | h | ⟨r, j, hj, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · subst cs
    have hR : (univ : Finset (Fin 4)) \ marked pathDistance 3 {0} = {3} := by decide
    cases r with
    | zero =>
      have hd := nonzero_draw hm (⟨1, by simp⟩ : Fin 2)
      have hd' : centreDraw pathDistance 3 false {0} j ≠ 0 := by
        simpa [List.replicate_succ, List.get_eq_getElem] using hd
      have hj3 : j = 3 := by
        by_contra hj3
        simp [centreDraw, hR, hj3] at hd'
      simp [hj3, List.replicate_succ]
    | succ r =>
      have hd := nonzero_draw hm
        (⟨1, by simp⟩ : Fin (List.replicate (r + 1 + 1) (0 : Fin 4) ++ [j]).length)
      have hd' : centreDraw (pathDistance (n := 4)) 3 false {0} 0 ≠ 0 := by
        simpa [List.replicate_succ, List.get_eq_getElem] using hd
      norm_num [centreDraw, hR] at hd'

private theorem repaired_off (S : Finset (Fin 4))
    (hS : S ∉ fourPathRepairedCentreSets) :
    terminalCentres pathDistance 3 false S = 0 := by
  classical
  unfold terminalCentres
  calc
    (∑' t : ℕ, ∑ z : Fin t → Fin 4,
        if (List.ofFn z).toFinset = S then
          traceMass pathDistance 3 false (List.ofFn z) else 0) =
      ∑' _t : ℕ, (0 : ℝ) := by
        apply tsum_congr
        intro t
        apply Finset.sum_eq_zero
        intro z _
        by_cases hs : (List.ofFn z).toFinset = S
        · rw [if_pos hs]
          by_contra hm
          apply hS
          have hmem : S ∈ fourPathRepairedCentreSets := by
            rcases repaired_classify (List.ofFn z) hm with h | h | h | h
            · have hset : S = ({1} : Finset (Fin 4)) := by simpa [h] using hs.symm
              simp [fourPathRepairedCentreSets, hset]
            · have hset : S = ({2} : Finset (Fin 4)) := by simpa [h] using hs.symm
              simp [fourPathRepairedCentreSets, hset]
            · have hset : S = ({0, 3} : Finset (Fin 4)) := by
                simpa [h, Finset.pair_comm] using hs.symm
              simp [fourPathRepairedCentreSets, hset]
            · have hset : S = ({0, 3} : Finset (Fin 4)) := by
                simpa [h, Finset.pair_comm] using hs.symm
              simp [fourPathRepairedCentreSets, hset]
          exact hmem
        · rw [if_neg hs]
    _ = 0 := tsum_zero

end
end SAP.P045a.WH.W2.P.T10_L1

theorem SAP.P045a.WH.W2.T10_L1_proof : SAP.P045a.WH.W2.T10_L1 := by
  constructor
  · intro S hS
    exact SAP.P045a.WH.W2.P.T10_L1.coded_off S hS
  · intro S hS
    exact SAP.P045a.WH.W2.P.T10_L1.repaired_off S hS
