import SAP.P044.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044.WH.W1.P.T2_L1

open Finset
open scoped BigOperators

private def mate (n : ℕ) (i : Fin (SAP.P044.w1MatchingN n)) : Fin (SAP.P044.w1MatchingN n) :=
  ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, by
    have hi : i.val < 2 * (n + 3) := by
      simpa [SAP.P044.w1MatchingN] using i.isLt
    change (if i.val % 2 = 0 then i.val + 1 else i.val - 1) < 2 * (n + 3)
    rcases Nat.mod_two_eq_zero_or_one i.val with h | h
    · simp only [h, ↓reduceIte]
      omega
    · have hne : i.val % 2 ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      omega⟩

private theorem mate_ne (n : ℕ) (i : Fin (SAP.P044.w1MatchingN n)) : mate n i ≠ i := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [mate] at hval
  split_ifs at hval <;> omega

private theorem mate_pair (n : ℕ) (i : Fin (SAP.P044.w1MatchingN n)) :
    (mate n i).val / 2 = i.val / 2 := by
  dsimp [mate]
  split_ifs with h <;> omega

private theorem pair_ne_eq_mate (n : ℕ) (i j : Fin (SAP.P044.w1MatchingN n))
    (hp : i.val / 2 = j.val / 2) (hij : i ≠ j) : j = mate n i := by
  apply Fin.ext
  dsimp [mate]
  have hji : j.val ≠ i.val := by
    intro h
    exact hij (Fin.ext h.symm)
  split_ifs with h <;> omega

private theorem matching_peerCount (n : ℕ) (s : Fin (SAP.P044.w1MatchingR n))
    (i : Fin (SAP.P044.w1MatchingN n)) :
    SAP.P044.peerCount (SAP.P044.w1MatchingAdj n) (SAP.P044.w1MatchingAssignments n s) i =
      if SAP.P044.w1MatchingAssignments n s (mate n i) then 1 else 0 := by
  classical
  unfold SAP.P044.peerCount
  rw [Finset.sum_eq_single_of_mem (mate n i) (Finset.mem_univ _)]
  · have hne : i ≠ mate n i := fun h => mate_ne n i h.symm
    simp [SAP.P044.w1MatchingAdj, hne, mate_pair]
  · intro j hj hji
    have hfalse : ¬(SAP.P044.w1MatchingAdj n i j &&
        SAP.P044.w1MatchingAssignments n s j) := by
      intro h
      have hand : SAP.P044.w1MatchingAdj n i j = true ∧
          SAP.P044.w1MatchingAssignments n s j = true := by
        simpa only [Bool.and_eq_true] using h
      have hadj : SAP.P044.w1MatchingAdj n i j = true := hand.1
      have ⟨hneq, hpair⟩ : i ≠ j ∧ i.val / 2 = j.val / 2 := by
        simpa [SAP.P044.w1MatchingAdj] using hadj
      have : j = mate n i := pair_ne_eq_mate n i j hpair hneq
      exact hji this
    simp [hfalse]

private theorem matching_assignment_pair (n : ℕ) (s : Fin (SAP.P044.w1MatchingR n))
    (i j : Fin (SAP.P044.w1MatchingN n)) (h : i.val / 2 = j.val / 2) :
    SAP.P044.w1MatchingAssignments n s i = SAP.P044.w1MatchingAssignments n s j := by
  by_cases hi : i.val ≤ 1
  · have hj : j.val ≤ 1 := by omega
    simp [SAP.P044.w1MatchingAssignments, hi, hj]
  · have hj : ¬ j.val ≤ 1 := by omega
    simp [SAP.P044.w1MatchingAssignments, hi, hj, h]

private theorem matching_exposure (n : ℕ) (s : Fin (SAP.P044.w1MatchingR n))
    (i : Fin (SAP.P044.w1MatchingN n)) :
    SAP.P044.w1MatchingF n s i =
      if SAP.P044.w1MatchingAssignments n s i then SAP.P044.Exposure.d11 else SAP.P044.Exposure.d00 := by
  have hassign := matching_assignment_pair n s i (mate n i) (mate_pair n i).symm
  unfold SAP.P044.w1MatchingF SAP.P044.exposure
  rw [matching_peerCount]
  rw [← hassign]
  cases SAP.P044.w1MatchingAssignments n s i <;> simp

private theorem assignment_injective (n : ℕ) :
    Function.Injective (SAP.P044.w1MatchingAssignments n) := by
  intro s t h
  change Fin (2 * (n + 2)) at s t
  let bs : Fin 2 × Fin (n + 2) := finProdFinEquiv.symm s
  let bt : Fin 2 × Fin (n + 2) := finProdFinEquiv.symm t
  have hzero : (SAP.P044.w1MatchingAssignments n s) ⟨0, by
      unfold SAP.P044.w1MatchingN
      omega⟩ =
      (SAP.P044.w1MatchingAssignments n t) ⟨0, by
      unfold SAP.P044.w1MatchingN
      omega⟩ := congrFun h ⟨0, by
        unfold SAP.P044.w1MatchingN
        omega⟩
  have hzero' : decide (bs.1 = 1) = decide (bt.1 = 1) := by
    simpa [SAP.P044.w1MatchingAssignments, bs, bt] using hzero
  have hbit : bs.1 = bt.1 := by
    by_cases hb : bs.1 = 1
    · by_cases ht : bt.1 = 1
      · exact hb.trans ht.symm
      · simp [hb, ht] at hzero'
    · by_cases ht : bt.1 = 1
      · simp [hb, ht] at hzero'
      · apply Fin.ext
        have hbs0 : bs.1.val = 0 := by
          have hn : bs.1.val ≠ 1 := by
            intro hval
            exact hb (Fin.ext hval)
          omega
        have hbt0 : bt.1.val = 0 := by
          have hn : bt.1.val ≠ 1 := by
            intro hval
            exact ht (Fin.ext hval)
          omega
        omega
  let v : Fin (SAP.P044.w1MatchingN n) :=
    ⟨2 * (bs.2.val + 1), by
      unfold SAP.P044.w1MatchingN
      have hb := bs.2.isLt
      omega⟩
  have hvdiv : v.val / 2 = bs.2.val + 1 := by
    dsimp [v]
    omega
  have hvpos : v.val / 2 ≠ 0 := by omega
  have hordinary : (SAP.P044.w1MatchingAssignments n s) v =
      (SAP.P044.w1MatchingAssignments n t) v := congrFun h v
  change decide (if v.val / 2 = 0 then bs.1 = 1 else v.val / 2 = bs.2.val + 1) =
      decide (if v.val / 2 = 0 then bt.1 = 1 else v.val / 2 = bt.2.val + 1) at hordinary
  simp [hvdiv] at hordinary
  have hidx : bs.2.val + 1 = bt.2.val + 1 := by omega
  have hsecond : bs.2 = bt.2 := Fin.ext (by omega)
  have hbs : bs = bt := Prod.ext hbit hsecond
  have hst : finProdFinEquiv.symm s = finProdFinEquiv.symm t := hbs
  exact finProdFinEquiv.symm.injective hst

private theorem matching_tau (n : ℕ) :
    SAP.P044.tau (SAP.P044.w1MatchingY n) SAP.P044.Exposure.d11 SAP.P044.Exposure.d00 = 0 := by
  simp [SAP.P044.tau, SAP.P044.w1MatchingY]

end SAP.P044.WH.W1.P.T2_L1

theorem SAP.P044.WH.W1.T2_L1_proof : SAP.P044.WH.W1.T2_L1 := by
  intro n
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp [SAP.P044.w1MatchingAdj, and_comm, eq_comm]
  · intro i
    constructor
    · simp [SAP.P044.w1MatchingAdj]
    · exact ⟨SAP.P044.WH.W1.P.T2_L1.mate n i, by
        have hne : i ≠ SAP.P044.WH.W1.P.T2_L1.mate n i :=
          fun h => SAP.P044.WH.W1.P.T2_L1.mate_ne n i h.symm
        simp [SAP.P044.w1MatchingAdj, hne, SAP.P044.WH.W1.P.T2_L1.mate_pair]⟩
  · exact SAP.P044.WH.W1.P.T2_L1.assignment_injective n
  · intro s i
    exact SAP.P044.WH.W1.P.T2_L1.matching_exposure n s i
  · exact SAP.P044.WH.W1.P.T2_L1.matching_tau n
