import AronowAudit.P022.Wave1.SharpBoundsBlueprint

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.SharpBounds
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem n8_proof : N8 := by
  intro h N _ y
  classical
  obtain ⟨hp, _, hm⟩ := h y
  have hnonneg (j : Fin N) : 0 ≤ sortedIncrement y j := by
    unfold sortedIncrement
    split_ifs with hj
    · exact sub_nonneg.mpr (hm (show (⟨j.val - 1, by omega⟩ : Fin N) ≤ j by
        exact Nat.sub_le _ _))
    · exact le_rfl
  refine ⟨hnonneg, ?_⟩
  intro x hx
  have hmem : x ∈ List.ofFn y := (List.mem_ofFn' y _).2 hx
  have hx' : x ∈ List.ofFn (sortedValues y) := hp.mem_iff.mpr hmem
  obtain ⟨r, hr⟩ := (List.mem_ofFn' (sortedValues y) _).1 hx'
  subst x
  let b : ℕ → ℝ := fun j => if hj : j < N then sortedIncrement y ⟨j, hj⟩ else 0
  have htel : ∀ n (hn : n < N), (∑ j ∈ range (n + 1), b j) =
      sortedValues y ⟨n, hn⟩ - sortedValues y 0 := by
    intro n
    induction n with
    | zero =>
      intro hn
      simp [b, sortedIncrement]
    | succ n ih =>
      intro hn
      rw [sum_range_succ, ih (by omega)]
      simp only [b, dif_pos hn, sortedIncrement, Nat.succ_pos, if_pos,
        Nat.add_one_sub_one]
      ring
  let f : ℕ → ℝ := fun j => if hj : j < N then sortedIncrement y ⟨j, hj⟩ *
      (if sortedValues y ⟨j, hj⟩ ≤ sortedValues y r then 1 else 0) else 0
  have hz (j : ℕ) (hj : j < N) (hrj : r.val < j) : f j = 0 := by
    dsimp [f]
    rw [dif_pos hj]
    by_cases hv : sortedValues y ⟨j, hj⟩ ≤ sortedValues y r
    · have hj0 : 0 < j := by omega
      have hprev : sortedValues y r ≤ sortedValues y ⟨j - 1, by omega⟩ :=
        hm (show r ≤ (⟨j - 1, by omega⟩ : Fin N) by show r.val ≤ j - 1; omega)
      have hnext : sortedValues y ⟨j - 1, by omega⟩ ≤ sortedValues y ⟨j, hj⟩ :=
        hm (show (⟨j - 1, by omega⟩ : Fin N) ≤ ⟨j, hj⟩ by exact Nat.sub_le _ _)
      simp only [if_pos hv, mul_one, sortedIncrement, if_pos hj0]
      linarith
    · simp [hv]
  have hearly (j : ℕ) (hj : j < r.val + 1) : f j = b j := by
    have hjN : j < N := lt_of_lt_of_le hj (Nat.succ_le_of_lt r.isLt)
    have hs : sortedValues y ⟨j, hjN⟩ ≤ sortedValues y r :=
      hm (show (⟨j, hjN⟩ : Fin N) ≤ r by show j ≤ r.val; omega)
    simp [f, b, hjN, hs]
  symm
  calc
    (∑ j, sortedIncrement y j * (if sortedValues y j ≤ sortedValues y r then (1 : ℝ) else 0)) =
        ∑ j ∈ range N, f j := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro j _
      simp [f, j.isLt]
    _ = ∑ j ∈ range (r.val + 1), f j := by
      symm
      apply sum_subset (range_mono (Nat.succ_le_of_lt r.isLt))
      intro j hj hjr
      exact hz j (mem_range.mp hj) (by simp only [mem_range] at hjr; omega)
    _ = ∑ j ∈ range (r.val + 1), b j :=
      sum_congr rfl (fun j hj => hearly j (mem_range.mp hj))
    _ = sortedValues y r - sortedValues y 0 := htel r.val r.isLt

end
end AronowAudit.P022.Wave1.SharpBounds
