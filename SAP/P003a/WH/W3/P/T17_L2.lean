import SAP.P003a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W3.P.T17_L2

open SAP.P003a

private lemma observed_treated (z : Assignment 5 2) (hz : (0 : Fin 5) ∈ z.val) :
    unitObserved (unitOutcomes wholeOneControlTable z.val) z.val = ⟨0,2,0,3⟩ := by
  have ha : (Finset.univ.filter fun i : Fin 5 =>
      i ∈ z.val ∧ unitOutcomes wholeOneControlTable z.val i = true) = ∅ := by
    ext i
    by_cases hi : i ∈ z.val
    · by_cases hzero : i = 0
      · subst i
        simp [unitOutcomes, wholeOneControlTable, hi]
      · simp [unitOutcomes, wholeOneControlTable, hi, hzero]
    · simp [hi]
  have hb : (Finset.univ.filter fun i : Fin 5 =>
      i ∈ z.val ∧ unitOutcomes wholeOneControlTable z.val i = false) = z.val := by
    ext i
    by_cases hi : i ∈ z.val
    · by_cases hzero : i = 0
      · subst i
        simp [unitOutcomes, wholeOneControlTable, hi]
      · simp [unitOutcomes, wholeOneControlTable, hi, hzero]
    · simp [hi]
  have hc : (Finset.univ.filter fun i : Fin 5 =>
      i ∉ z.val ∧ unitOutcomes wholeOneControlTable z.val i = true) = ∅ := by
    ext i
    by_cases hi : i ∈ z.val
    · by_cases hzero : i = 0
      · subst i
        simp [unitOutcomes, wholeOneControlTable, hi]
      · simp [unitOutcomes, wholeOneControlTable, hi, hzero]
    · by_cases hzero : i = 0 <;> simp [unitOutcomes, wholeOneControlTable, hi, hzero, hz]
  have hd : (Finset.univ.filter fun i : Fin 5 =>
      i ∉ z.val ∧ unitOutcomes wholeOneControlTable z.val i = false) =
        Finset.univ \ z.val := by
    ext i
    by_cases hi : i ∈ z.val
    · by_cases hzero : i = 0
      · subst i
        simp [unitOutcomes, wholeOneControlTable, hi]
      · simp [unitOutcomes, wholeOneControlTable, hi, hzero]
    · by_cases hzero : i = 0 <;> simp [unitOutcomes, wholeOneControlTable, hi, hzero, hz]
  have hcard : (Finset.univ \ z.val).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ z.val), Finset.card_univ,
      z.property]
    decide
  ext <;> simp [unitObserved, ha, hb, hc, hd, z.property, hcard]

private lemma observed_untreated (z : Assignment 5 2) (hz : (0 : Fin 5) ∉ z.val) :
    unitObserved (unitOutcomes wholeOneControlTable z.val) z.val = ⟨0,2,1,2⟩ := by
  have ha : (Finset.univ.filter fun i : Fin 5 =>
      i ∈ z.val ∧ unitOutcomes wholeOneControlTable z.val i = true) = ∅ := by
    ext i
    by_cases hi : i ∈ z.val
    · by_cases hzero : i = 0
      · subst i
        simp [unitOutcomes, wholeOneControlTable, hi]
      · simp [unitOutcomes, wholeOneControlTable, hi, hzero]
    · simp [hi]
  have hb : (Finset.univ.filter fun i : Fin 5 =>
      i ∈ z.val ∧ unitOutcomes wholeOneControlTable z.val i = false) = z.val := by
    ext i
    by_cases hi : i ∈ z.val
    · by_cases hzero : i = 0
      · subst i
        simp [unitOutcomes, wholeOneControlTable, hi]
      · simp [unitOutcomes, wholeOneControlTable, hi, hzero]
    · simp [hi]
  have hc : (Finset.univ.filter fun i : Fin 5 =>
      i ∉ z.val ∧ unitOutcomes wholeOneControlTable z.val i = true) = {0} := by
    ext i
    by_cases hi : i ∈ z.val
    · by_cases hzero : i = 0
      · subst i
        exact (hz hi).elim
      · simp [unitOutcomes, wholeOneControlTable, hi, hzero]
    · by_cases hzero : i = 0 <;> simp [unitOutcomes, wholeOneControlTable, hi, hzero, hz]
  have hd : (Finset.univ.filter fun i : Fin 5 =>
      i ∉ z.val ∧ unitOutcomes wholeOneControlTable z.val i = false) =
        Finset.univ \ (insert 0 z.val) := by
    ext i
    by_cases hi : i ∈ z.val
    · by_cases hzero : i = 0
      · subst i
        exact (hz hi).elim
      · simp [unitOutcomes, wholeOneControlTable, hi, hzero]
    · by_cases hzero : i = 0 <;> simp [unitOutcomes, wholeOneControlTable, hi, hzero, hz]
  have hins : (insert (0 : Fin 5) z.val).card = 3 := by
    rw [Finset.card_insert_of_notMem hz, z.property]
  have hcard : (Finset.univ \ (insert (0 : Fin 5) z.val)).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ (insert (0 : Fin 5) z.val)),
      Finset.card_univ, hins]
    decide
  ext <;> simp [unitObserved, ha, hb, hc, hd, z.property, hcard]

end SAP.P003a.WH.W3.P.T17_L2

theorem SAP.P003a.WH.W3.T17_L2_proof : SAP.P003a.WH.W3.T17_L2 := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · intro z
    by_cases hz : (0 : Fin 5) ∈ z.val
    · constructor
      · exact fun _ => SAP.P003a.WH.W3.P.T17_L2.observed_treated z hz
      · intro h
        exact (h hz).elim
    · constructor
      · intro h
        exact (hz h).elim
      · exact fun _ => SAP.P003a.WH.W3.P.T17_L2.observed_untreated z hz
