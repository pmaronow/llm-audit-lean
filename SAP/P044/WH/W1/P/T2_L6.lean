import SAP.P044.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044.WH.W1.P.T2_L6

open Finset
open scoped BigOperators

noncomputable section

private theorem assign_eq_of_small (n : ℕ) (s : Fin (w1MatchingR n))
    (i j : Fin (w1MatchingN n)) (hi : i.val < 2) (hj : j.val < 2) :
    w1MatchingAssignments n s i = w1MatchingAssignments n s j := by
  have hli : i.val ≤ 1 := by omega
  have hlj : j.val ≤ 1 := by omega
  simp [w1MatchingAssignments, hli, hlj]

private def covSummand (n : ℕ) (e : Equiv.Perm (Fin (w1MatchingR n)))
    (s : Fin (w1MatchingR n)) (i j : Fin (w1MatchingN n)) : ℚ :=
  (if 0 < w1MatchingQ n e i j .d11 .d00 then
    (if w1MatchingF n s i = .d11 ∧ w1MatchingF n s j = .d00 then
      w1MatchingY n i .d11 * w1MatchingY n j .d00 *
        (1 / (w1MatchingW n e i .d11 * w1MatchingW n e j .d00) -
          1 / w1MatchingQ n e i j .d11 .d00) else 0)
    else 0) -
  (if w1MatchingQ n e i j .d11 .d00 = 0 then
    (if w1MatchingF n s i = .d11 then
      w1MatchingY n i .d11 ^ 2 / (2 * w1MatchingW n e i .d11) else 0) +
    (if w1MatchingF n s j = .d00 then
      w1MatchingY n j .d00 ^ 2 / (2 * w1MatchingW n e j .d00) else 0)
    else 0)

private theorem covSummand_eq (n : ℕ) (hg : W1MatchingGeometry n)
    (hin : W1MatchingInputs n) (e : Equiv.Perm (Fin (w1MatchingR n)))
    (s : Fin (w1MatchingR n)) (i j : Fin (w1MatchingN n)) :
    covSummand n e s i j =
      if i.val ≤ 1 ∧ j.val ≤ 1 then -(1 / (2 * w1MatchingWeight n)) else 0 := by
  rcases hin with ⟨_, _, _, hweight, hjoint, hmixed⟩
  by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2
  · have hq : w1MatchingQ n e i j .d11 .d00 = 0 := by
      simpa using hjoint e i j .d11 .d00 hi hj (Or.inl rfl) (Or.inr rfl)
    have hw1 : w1MatchingW n e i .d11 = w1MatchingWeight n :=
      hweight e i .d11 hi (Or.inl rfl)
    have hw2 : w1MatchingW n e j .d00 = w1MatchingWeight n :=
      hweight e j .d00 hj (Or.inr rfl)
    have hassign := assign_eq_of_small n s i j hi hj
    rcases hg with ⟨_, _, _, hexp, _⟩
    have hli : i.val ≤ 1 := by omega
    have hlj : j.val ≤ 1 := by omega
    rw [covSummand, hq, hw1, hw2, hexp s i, hexp s j, hassign]
    by_cases hb : w1MatchingAssignments n s i
    · have hbj : w1MatchingAssignments n s j = true := by
        rw [← hassign]
        exact hb
      simp [hb, hbj, w1MatchingY, hli, hlj]
      <;> ring_nf
    · have hbi : w1MatchingAssignments n s i = false := by
        cases hval : w1MatchingAssignments n s i with
        | false => rfl
        | true => exact (hb hval).elim
      have hbj : w1MatchingAssignments n s j = false := by
        rw [← hassign]
        exact hbi
      simp [hbi, hbj, w1MatchingY, hli, hlj]
      <;> ring_nf
  · have hqj : 2 ≤ j.val := by omega
    have hqpos : 0 < w1MatchingQ n e i j .d11 .d00 :=
      hmixed e i j .d11 .d00 (Or.inl ⟨hi, hqj⟩) (Or.inl rfl) (Or.inr rfl)
    have hqne : w1MatchingQ n e i j .d11 .d00 ≠ 0 := ne_of_gt hqpos
    have hyi : w1MatchingY n i .d11 = 1 := by simp [w1MatchingY, hi]
    have hyj : w1MatchingY n j .d00 = 0 := by simp [w1MatchingY, hj]
    have hnotj : ¬ j.val ≤ 1 := by omega
    simp [covSummand, hqpos, hqne, hyj, hnotj]
  · have hqi : 2 ≤ i.val := by omega
    have hqpos : 0 < w1MatchingQ n e i j .d11 .d00 :=
      hmixed e i j .d11 .d00 (Or.inr ⟨hqi, hj⟩) (Or.inl rfl) (Or.inr rfl)
    have hqne : w1MatchingQ n e i j .d11 .d00 ≠ 0 := ne_of_gt hqpos
    have hyi : w1MatchingY n i .d11 = 0 := by simp [w1MatchingY, hi]
    have hyj : w1MatchingY n j .d00 = 1 := by simp [w1MatchingY, hj]
    have hnoti : ¬ i.val ≤ 1 := by omega
    simp [covSummand, hqpos, hqne, hyi, hnoti]
  · have hyi : w1MatchingY n i .d11 = 0 := by simp [w1MatchingY, hi]
    have hyj : w1MatchingY n j .d00 = 0 := by simp [w1MatchingY, hj]
    have hnoti : ¬ i.val ≤ 1 := by omega
    have hnotj : ¬ j.val ≤ 1 := by omega
    simp [covSummand, hyi, hyj, hnoti, hnotj]

private theorem sum_small_indicator (n : ℕ) (c : ℚ) :
    (∑ i : Fin (w1MatchingN n), if i.val ≤ 1 then c else 0) = 2 * c := by
  classical
  have hN : 2 ≤ w1MatchingN n := by
    unfold w1MatchingN
    omega
  let i0 : Fin (w1MatchingN n) := ⟨0, by omega⟩
  let i1 : Fin (w1MatchingN n) := ⟨1, by omega⟩
  have hfilter : Finset.univ.filter (fun i : Fin (w1MatchingN n) => i.val ≤ 1) = {i0, i1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hi
      have hv : i.val = 0 ∨ i.val = 1 := by omega
      rcases hv with hv | hv
      · left
        apply Fin.ext
        exact hv
      · right
        apply Fin.ext
        exact hv
    · rintro (hi | hi)
      · subst i
        simp [i0]
      · subst i
        simp [i1]
  rw [← Finset.sum_filter, hfilter]
  simp [i0, i1]

private theorem indicator_double_sum (n : ℕ) (c : ℚ) :
    (∑ i : Fin (w1MatchingN n), ∑ j : Fin (w1MatchingN n),
      if i.val ≤ 1 ∧ j.val ≤ 1 then c else 0) = 4 * c := by
  have hinner (i : Fin (w1MatchingN n)) :
      (∑ j : Fin (w1MatchingN n),
        if i.val ≤ 1 ∧ j.val ≤ 1 then c else 0) =
        if i.val ≤ 1 then 2 * c else 0 := by
    by_cases hi : i.val ≤ 1
    · simp [hi, sum_small_indicator]
    · simp [hi]
  calc
    (∑ i : Fin (w1MatchingN n), ∑ j : Fin (w1MatchingN n),
        if i.val ≤ 1 ∧ j.val ≤ 1 then c else 0) =
      ∑ i : Fin (w1MatchingN n), if i.val ≤ 1 then 2 * c else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        exact hinner i
    _ = 2 * (2 * c) := sum_small_indicator n (2 * c)
    _ = 4 * c := by ring

private theorem covariance_sum (n : ℕ) (hg : W1MatchingGeometry n)
    (hin : W1MatchingInputs n) (e : Equiv.Perm (Fin (w1MatchingR n)))
    (s : Fin (w1MatchingR n)) :
    totalCovarianceEstimate (w1MatchingF n) (w1MatchingY n)
      (w1MatchingW n e) (w1MatchingQ n e) .d11 .d00 s =
        -2 / w1MatchingWeight n := by
  change (∑ i : Fin (w1MatchingN n), ∑ j : Fin (w1MatchingN n),
    covSummand n e s i j) = -2 / w1MatchingWeight n
  simp_rw [covSummand_eq n hg hin e s]
  rw [indicator_double_sum]
  have hw : 0 < w1MatchingWeight n := by
    unfold w1MatchingWeight
    positivity
  field_simp
  <;> ring

end
end SAP.P044.WH.W1.P.T2_L6

theorem SAP.P044.WH.W1.T2_L6_proof : SAP.P044.WH.W1.T2_L6 := by
  intro n hg hin e s
  exact SAP.P044.WH.W1.P.T2_L6.covariance_sum n hg hin e s
