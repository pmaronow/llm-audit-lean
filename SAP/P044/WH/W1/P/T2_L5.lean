import SAP.P044.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace SAP.P044.WH.W1.P.T2_L5

open Finset
open scoped BigOperators

private def d0 (n : ℕ) : Fin (SAP.P044.w1MatchingN n) :=
  ⟨0, by unfold SAP.P044.w1MatchingN; omega⟩

private def d1 (n : ℕ) : Fin (SAP.P044.w1MatchingN n) :=
  ⟨1, by unfold SAP.P044.w1MatchingN; omega⟩

private def dset (n : ℕ) : Finset (Fin (SAP.P044.w1MatchingN n)) :=
  {d0 n, d1 n}

private def varianceTerm (n : ℕ) (e : Equiv.Perm (Fin (SAP.P044.w1MatchingR n)))
    (s : Fin (SAP.P044.w1MatchingR n)) (a : Exposure)
    (i j : Fin (SAP.P044.w1MatchingN n)) : ℚ :=
  (if 0 < SAP.P044.w1MatchingQ n e i j a a then
    (if SAP.P044.w1MatchingF n s i = a ∧ SAP.P044.w1MatchingF n s j = a then
      SAP.P044.w1MatchingY n i a * SAP.P044.w1MatchingY n j a *
        (1 / (SAP.P044.w1MatchingW n e i a * SAP.P044.w1MatchingW n e j a) -
          1 / SAP.P044.w1MatchingQ n e i j a a) else 0)
    else 0) +
  (if i ≠ j ∧ SAP.P044.w1MatchingQ n e i j a a = 0 then
    (if SAP.P044.w1MatchingF n s i = a then
      SAP.P044.w1MatchingY n i a ^ 2 / (2 * SAP.P044.w1MatchingW n e i a) else 0) +
    (if SAP.P044.w1MatchingF n s j = a then
      SAP.P044.w1MatchingY n j a ^ 2 / (2 * SAP.P044.w1MatchingW n e j a) else 0)
    else 0)

private theorem dset_eq_filter (n : ℕ) :
    dset n = Finset.univ.filter (fun i : Fin (SAP.P044.w1MatchingN n) => i.val < 2) := by
  ext i
  simp only [dset, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro (h | h)
    · have hv : i.val = 0 := congrArg Fin.val h
      omega
    · have hv : i.val = 1 := congrArg Fin.val h
      omega
  · intro h
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    rcases hv with hv | hv
    · left
      apply Fin.ext
      simpa [d0] using hv
    · right
      apply Fin.ext
      simpa [d1] using hv

private theorem assignment_d0_d1 (n : ℕ) (s : Fin (SAP.P044.w1MatchingR n)) :
    SAP.P044.w1MatchingAssignments n s (d0 n) =
      SAP.P044.w1MatchingAssignments n s (d1 n) := by
  simp [SAP.P044.w1MatchingAssignments, d0, d1]

private theorem varianceTerm_zero_outside (n : ℕ)
    (hin : SAP.P044.W1MatchingInputs n) (e : Equiv.Perm (Fin (SAP.P044.w1MatchingR n)))
    (s : Fin (SAP.P044.w1MatchingR n)) (a : Exposure)
    (ha : a = .d11 ∨ a = .d00)
    (i j : Fin (SAP.P044.w1MatchingN n))
    (h : ¬ i.val < 2 ∨ ¬ j.val < 2) : varianceTerm n e s a i j = 0 := by
  rcases hin with ⟨hwp, hqnonneg, hdiag, hwDist, hqDist, hmix⟩
  by_cases hi : i.val < 2
  · rcases h with hni | hnj
    · exact (hni hi).elim
    · have hm : (i.val < 2 ∧ 2 ≤ j.val) ∨ (2 ≤ i.val ∧ j.val < 2) :=
        Or.inl ⟨hi, Nat.le_of_not_lt hnj⟩
      have hpos := hmix e i j a a hm ha ha
      have hyj : SAP.P044.w1MatchingY n j a = 0 := by
        simp [SAP.P044.w1MatchingY]
        omega
      simp [varianceTerm, hyj, hpos, ne_of_gt hpos]
  · have hyi : SAP.P044.w1MatchingY n i a = 0 := by
      simp [SAP.P044.w1MatchingY]
      omega
    by_cases hj : j.val < 2
    · have hm : (i.val < 2 ∧ 2 ≤ j.val) ∨ (2 ≤ i.val ∧ j.val < 2) :=
        Or.inr ⟨Nat.le_of_not_lt hi, hj⟩
      have hpos := hmix e i j a a hm ha ha
      simp [varianceTerm, hyi, hpos, ne_of_gt hpos]
    · have hyj : SAP.P044.w1MatchingY n j a = 0 := by
        simp [SAP.P044.w1MatchingY]
        omega
      simp [varianceTerm, hyi, hyj]

private theorem totalVariance_reduce (n : ℕ)
    (hin : SAP.P044.W1MatchingInputs n) (e : Equiv.Perm (Fin (SAP.P044.w1MatchingR n)))
    (s : Fin (SAP.P044.w1MatchingR n)) (a : Exposure)
    (ha : a = .d11 ∨ a = .d00) :
    SAP.P044.totalVarianceEstimate (SAP.P044.w1MatchingF n) (SAP.P044.w1MatchingY n)
      (SAP.P044.w1MatchingW n e) (SAP.P044.w1MatchingQ n e) a s =
      ∑ i ∈ dset n, ∑ j ∈ dset n, varianceTerm n e s a i j := by
  unfold SAP.P044.totalVarianceEstimate
  change (∑ i : Fin (SAP.P044.w1MatchingN n), ∑ j, varianceTerm n e s a i j) = _
  have houter : (∑ i : Fin (SAP.P044.w1MatchingN n), ∑ j, varianceTerm n e s a i j) =
      ∑ i ∈ dset n, ∑ j, varianceTerm n e s a i j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ (dset n))
    intro i hi hnot
    apply Finset.sum_eq_zero
    intro j hj
    apply varianceTerm_zero_outside n hin e s a ha i j
    by_contra hb
    apply hnot
    rw [dset_eq_filter]
    simp
    omega
  calc
    ∑ i : Fin (SAP.P044.w1MatchingN n), ∑ j, varianceTerm n e s a i j =
        ∑ i ∈ dset n, ∑ j, varianceTerm n e s a i j := houter
    _ = ∑ i ∈ dset n, ∑ j ∈ dset n, varianceTerm n e s a i j := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      apply Finset.sum_subset (Finset.subset_univ (dset n))
      intro j hj hnot
      apply varianceTerm_zero_outside n hin e s a ha i j
      by_contra hb
      apply hnot
      rw [dset_eq_filter]
      simp
      omega

private theorem totalVariance_eval (n : ℕ)
    (hg : SAP.P044.W1MatchingGeometry n) (hin : SAP.P044.W1MatchingInputs n)
    (e : Equiv.Perm (Fin (SAP.P044.w1MatchingR n)))
    (s : Fin (SAP.P044.w1MatchingR n)) (a : Exposure)
    (ha : a = .d11 ∨ a = .d00) :
    SAP.P044.totalVarianceEstimate (SAP.P044.w1MatchingF n) (SAP.P044.w1MatchingY n)
      (SAP.P044.w1MatchingW n e) (SAP.P044.w1MatchingQ n e) a s =
      if SAP.P044.w1MatchingF n s (d0 n) = a then
        4 / SAP.P044.w1MatchingWeight n ^ 2 - 2 / SAP.P044.w1MatchingWeight n -
          2 / SAP.P044.w1MatchingJoint n
      else 0 := by
  have hfd : SAP.P044.w1MatchingF n s (d0 n) = SAP.P044.w1MatchingF n s (d1 n) := by
    rw [hg.2.2.2.1, hg.2.2.2.1, assignment_d0_d1]
  have hfdCase : SAP.P044.w1MatchingF n s (d0 n) = .d11 ∨
      SAP.P044.w1MatchingF n s (d0 n) = .d00 := by
    rw [hg.2.2.2.1]
    split_ifs <;> simp
  have hw0 := hin.2.2.2.1 e (d0 n) a (by simp [d0]) ha
  have hw1 := hin.2.2.2.1 e (d1 n) a (by simp [d1]) ha
  have hq00 := hin.2.2.2.2.1 e (d0 n) (d0 n) a a (by simp [d0]) (by simp [d0]) ha ha
  have hq01 := hin.2.2.2.2.1 e (d0 n) (d1 n) a a (by simp [d0]) (by simp [d1]) ha ha
  have hq10 := hin.2.2.2.2.1 e (d1 n) (d0 n) a a (by simp [d1]) (by simp [d0]) ha ha
  have hq11 := hin.2.2.2.2.1 e (d1 n) (d1 n) a a (by simp [d1]) (by simp [d1]) ha ha
  have hw0val : SAP.P044.w1MatchingW n e (d0 n) a = SAP.P044.w1MatchingWeight n := hw0
  have hw1val : SAP.P044.w1MatchingW n e (d1 n) a = SAP.P044.w1MatchingWeight n := hw1
  have hq00val : SAP.P044.w1MatchingQ n e (d0 n) (d0 n) a a = SAP.P044.w1MatchingWeight n := by
    simpa [d0] using hq00
  have hq11val : SAP.P044.w1MatchingQ n e (d1 n) (d1 n) a a = SAP.P044.w1MatchingWeight n := by
    simpa [d1] using hq11
  have hq01val : SAP.P044.w1MatchingQ n e (d0 n) (d1 n) a a = SAP.P044.w1MatchingJoint n := by
    simpa [d0, d1] using hq01
  have hq10val : SAP.P044.w1MatchingQ n e (d1 n) (d0 n) a a = SAP.P044.w1MatchingJoint n := by
    simpa [d0, d1] using hq10
  have hwpos : 0 < SAP.P044.w1MatchingWeight n := by
    rw [← hw0val]
    exact hin.1 e (d0 n) a
  have hqjointpos : 0 < SAP.P044.w1MatchingJoint n := by
    unfold SAP.P044.w1MatchingJoint
    positivity
  have hy0 : SAP.P044.w1MatchingY n (d0 n) a = 1 := by simp [SAP.P044.w1MatchingY, d0]
  have hy1 : SAP.P044.w1MatchingY n (d1 n) a = 1 := by simp [SAP.P044.w1MatchingY, d1]
  have hneq : d0 n ≠ d1 n := by
    intro h
    have hv := congrArg Fin.val h
    simp [d0, d1] at hv
  have ht00 : varianceTerm n e s a (d0 n) (d0 n) =
      if SAP.P044.w1MatchingF n s (d0 n) = a then
        1 / (SAP.P044.w1MatchingWeight n * SAP.P044.w1MatchingWeight n) -
          1 / SAP.P044.w1MatchingWeight n else 0 := by
    simp [varianceTerm, hw0val, hq00val, hy0, hwpos]
  have ht11 : varianceTerm n e s a (d1 n) (d1 n) =
      if SAP.P044.w1MatchingF n s (d0 n) = a then
        1 / (SAP.P044.w1MatchingWeight n * SAP.P044.w1MatchingWeight n) -
          1 / SAP.P044.w1MatchingWeight n else 0 := by
    simp [varianceTerm, hfd.symm, hw1val, hq11val, hy1, hwpos, ne_of_gt hwpos]
  have ht01 : varianceTerm n e s a (d0 n) (d1 n) =
      if SAP.P044.w1MatchingF n s (d0 n) = a then
        1 / (SAP.P044.w1MatchingWeight n * SAP.P044.w1MatchingWeight n) -
          1 / SAP.P044.w1MatchingJoint n else 0 := by
    simp [varianceTerm, hfd.symm, hw0val, hw1val, hq01val, hy0, hy1, hneq,
      hneq.symm, hwpos, hqjointpos, ne_of_gt hqjointpos]
  have ht10 : varianceTerm n e s a (d1 n) (d0 n) =
      if SAP.P044.w1MatchingF n s (d0 n) = a then
        1 / (SAP.P044.w1MatchingWeight n * SAP.P044.w1MatchingWeight n) -
          1 / SAP.P044.w1MatchingJoint n else 0 := by
    simp [varianceTerm, hfd.symm, hw0val, hw1val, hq10val, hy0, hy1, hneq,
      hneq.symm, hwpos, hqjointpos, ne_of_gt hqjointpos]
  have hsum : (∑ i ∈ dset n, ∑ j ∈ dset n, varianceTerm n e s a i j) =
      varianceTerm n e s a (d0 n) (d0 n) + varianceTerm n e s a (d0 n) (d1 n) +
        varianceTerm n e s a (d1 n) (d0 n) + varianceTerm n e s a (d1 n) (d1 n) := by
    simp [dset, hneq]
    ac_rfl
  rw [totalVariance_reduce n hin e s a ha]
  rw [hsum, ht00, ht01, ht10, ht11]
  by_cases hp : SAP.P044.w1MatchingF n s (d0 n) = a
  · simp [hp]
    field_simp [hwpos.ne', hqjointpos.ne'] <;> ring
  · simp [hp]

private theorem matchingWithin (n : ℕ) (hg : SAP.P044.W1MatchingGeometry n)
    (hin : SAP.P044.W1MatchingInputs n) : SAP.P044.W1MatchingWithin n := by
  intro e s
  have hexposed : SAP.P044.w1MatchingF n s (d0 n) = .d11 ∨
      SAP.P044.w1MatchingF n s (d0 n) = .d00 := by
    rw [hg.2.2.2.1]
    split_ifs <;> simp
  change SAP.P044.totalVarianceEstimate (SAP.P044.w1MatchingF n)
      (SAP.P044.w1MatchingY n) (SAP.P044.w1MatchingW n e) (SAP.P044.w1MatchingQ n e)
      .d11 s +
    SAP.P044.totalVarianceEstimate (SAP.P044.w1MatchingF n)
      (SAP.P044.w1MatchingY n) (SAP.P044.w1MatchingW n e) (SAP.P044.w1MatchingQ n e)
      .d00 s = _
  rcases hexposed with h | h
  · rw [totalVariance_eval n hg hin e s .d11 (Or.inl rfl)]
    rw [totalVariance_eval n hg hin e s .d00 (Or.inr rfl)]
    simp [h]
  · rw [totalVariance_eval n hg hin e s .d11 (Or.inl rfl)]
    rw [totalVariance_eval n hg hin e s .d00 (Or.inr rfl)]
    simp [h]

theorem _root_.SAP.P044.WH.W1.T2_L5_proof : SAP.P044.WH.W1.T2_L5 := by
  intro n hg hin
  exact matchingWithin n hg hin
