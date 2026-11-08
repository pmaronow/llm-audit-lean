import SAP.P044.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044.WH.W1.P.T2_L4

open Finset
open scoped BigOperators

theorem sum_fin_eq_first_two {N : ℕ} (h0 : 0 < N) (h1 : 1 < N)
    (g : Fin N → ℚ) (hzero : ∀ i, 2 ≤ i.val → g i = 0) :
    (∑ i : Fin N, g i) = g ⟨0, h0⟩ + g ⟨1, h1⟩ := by
  classical
  let i0 : Fin N := ⟨0, h0⟩
  let i1 : Fin N := ⟨1, h1⟩
  have hne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    norm_num [i0, i1] at this
  let s : Finset (Fin N) := {i0, i1}
  have hs : s ⊆ Finset.univ := Finset.subset_univ _
  have hz : ∀ i ∈ Finset.univ, i ∉ s → g i = 0 := by
    intro i _ hi
    have hi0 : i ≠ i0 := by
      intro h
      apply hi
      simp [s, h]
    have hi1 : i ≠ i1 := by
      intro h
      apply hi
      simp [s, h]
    have hval0 : i.val ≠ 0 := by
      intro hv
      apply hi0
      apply Fin.ext
      exact hv
    have hval1 : i.val ≠ 1 := by
      intro hv
      apply hi1
      apply Fin.ext
      exact hv
    have hge : 2 ≤ i.val := by omega
    exact hzero i hge
  calc
    (∑ i : Fin N, g i) = ∑ i ∈ s, g i := (Finset.sum_subset hs hz).symm
    _ = g ⟨0, h0⟩ + g ⟨1, h1⟩ := by simp [s, i0, i1, hne]

end SAP.P044.WH.W1.P.T2_L4

open SAP.P044.WH.W1.P.T2_L4
open Finset
open scoped BigOperators

theorem SAP.P044.WH.W1.T2_L4_proof : SAP.P044.WH.W1.T2_L4 := by
  intro n hg hi e s
  let i0 : Fin (w1MatchingN n) := ⟨0, by unfold w1MatchingN; omega⟩
  let i1 : Fin (w1MatchingN n) := ⟨1, by unfold w1MatchingN; omega⟩
  let A : Bool := w1MatchingAssignments n s i0
  have hA1 : w1MatchingAssignments n s i1 = A := by
    simp [A, i0, i1, w1MatchingAssignments]
  have hF0 : w1MatchingF n s i0 = if A then Exposure.d11 else Exposure.d00 := by
    rw [hg.2.2.2.1 s i0]
  have hF1 : w1MatchingF n s i1 = if A then Exposure.d11 else Exposure.d00 := by
    rw [hg.2.2.2.1 s i1, hA1]
  have hY0 : w1MatchingY n i0 Exposure.d11 = 1 := by simp [w1MatchingY, i0]
  have hY1 : w1MatchingY n i1 Exposure.d11 = 1 := by simp [w1MatchingY, i1]
  have hweight0 (a : Exposure) (ha : a = Exposure.d11 ∨ a = Exposure.d00) :
      w1MatchingW n e i0 a = w1MatchingWeight n :=
    hi.2.2.2.1 e i0 a (by simp [i0]) ha
  have hweight1 (a : Exposure) (ha : a = Exposure.d11 ∨ a = Exposure.d00) :
      w1MatchingW n e i1 a = w1MatchingWeight n :=
    hi.2.2.2.1 e i1 a (by simp [i1]) ha
  have hterm0_11 :
      htTerm (w1MatchingF n) (w1MatchingY n) (w1MatchingW n e)
        Exposure.d11 s i0 = if A then 1 / w1MatchingWeight n else 0 := by
    cases hA : A <;>
      simp [htTerm, w1MatchingY, i0, hF0, hA,
        hweight0 Exposure.d11 (Or.inl rfl)]
  have hterm1_11 :
      htTerm (w1MatchingF n) (w1MatchingY n) (w1MatchingW n e)
        Exposure.d11 s i1 = if A then 1 / w1MatchingWeight n else 0 := by
    cases hA : A <;>
      simp [htTerm, w1MatchingY, i1, hF1, hA,
        hweight1 Exposure.d11 (Or.inl rfl)]
  have hterm0_00 :
      htTerm (w1MatchingF n) (w1MatchingY n) (w1MatchingW n e)
        Exposure.d00 s i0 = if A then 0 else 1 / w1MatchingWeight n := by
    cases hA : A <;>
      simp [htTerm, w1MatchingY, i0, hF0, hA,
        hweight0 Exposure.d00 (Or.inr rfl)]
  have hterm1_00 :
      htTerm (w1MatchingF n) (w1MatchingY n) (w1MatchingW n e)
        Exposure.d00 s i1 = if A then 0 else 1 / w1MatchingWeight n := by
    cases hA : A <;>
      simp [htTerm, w1MatchingY, i1, hF1, hA,
        hweight1 Exposure.d00 (Or.inr rfl)]
  have hN0 : 0 < w1MatchingN n := by unfold w1MatchingN; omega
  have hN1 : 1 < w1MatchingN n := by unfold w1MatchingN; omega
  have hsum11 :
      (∑ i : Fin (w1MatchingN n),
        htTerm (w1MatchingF n) (w1MatchingY n) (w1MatchingW n e)
          Exposure.d11 s i) = if A then 2 / w1MatchingWeight n else 0 := by
    rw [sum_fin_eq_first_two hN0 hN1 _ (by
      intro i h
      have hi2 : ¬ i.val < 2 := by omega
      have hy : w1MatchingY n i Exposure.d11 = 0 := by
        simp [w1MatchingY, hi2]
      simp [htTerm, hy])]
    rw [hterm0_11, hterm1_11]
    cases hA : A <;> simp [hA] <;> ring
  have hsum00 :
      (∑ i : Fin (w1MatchingN n),
        htTerm (w1MatchingF n) (w1MatchingY n) (w1MatchingW n e)
          Exposure.d00 s i) = if A then 0 else 2 / w1MatchingWeight n := by
    rw [sum_fin_eq_first_two hN0 hN1 _ (by
      intro i h
      have hi2 : ¬ i.val < 2 := by omega
      have hy : w1MatchingY n i Exposure.d00 = 0 := by
        simp [w1MatchingY, hi2]
      simp [htTerm, hy])]
    rw [hterm0_00, hterm1_00]
    cases hA : A <;> simp [hA] <;> ring
  have hNpos : (0 : ℚ) < (w1MatchingN n : ℚ) := by exact_mod_cast hN0
  have hwpos : (0 : ℚ) < w1MatchingWeight n := by
    have h := hi.1 e i0 Exposure.d11
    rw [hweight0 Exposure.d11 (Or.inl rfl)] at h
    exact h
  have hdiv :
      (2 / w1MatchingWeight n) / (w1MatchingN n : ℚ) =
        2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n) := by
    field_simp [ne_of_gt hNpos, ne_of_gt hwpos]
  have hmean11 :
      htMean (w1MatchingF n) (w1MatchingY n) (w1MatchingW n e)
        Exposure.d11 s = if A then
          2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n) else 0 := by
    unfold htMean
    rw [hsum11]
    cases hA : A <;> simp [hA, hdiv]
  have hmean00 :
      htMean (w1MatchingF n) (w1MatchingY n) (w1MatchingW n e)
        Exposure.d00 s = if A then 0 else
          2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n) := by
    unfold htMean
    rw [hsum00]
    cases hA : A <;> simp [hA, hdiv]
  change htContrast (w1MatchingF n) (w1MatchingY n) (w1MatchingW n e)
    Exposure.d11 Exposure.d00 s = if A then
      2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n) else
      -(2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n))
  rw [htContrast, hmean11, hmean00]
  cases hA : A <;> simp [hA] <;> ring

