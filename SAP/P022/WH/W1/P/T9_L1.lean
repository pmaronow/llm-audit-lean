import SAP.P022.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T9_L1

open SAP.P022.WH.W1
open scoped BigOperators

private noncomputable def grid (m k : ℕ) : Finset ℝ :=
  ((Finset.range (m + 1)).image (fun i : ℕ => (i : ℝ) / m)) ∪
    ((Finset.range (k + 1)).image (fun j : ℕ => (j : ℝ) / k))

private theorem grid_bounds {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    {x : ℝ} (hx : x ∈ grid m k) : 0 ≤ x ∧ x ≤ 1 := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i ≤ m := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    constructor
    · positivity
    · exact (div_le_one (by exact_mod_cast hm)).2 (by exact_mod_cast hi')
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i ≤ k := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    constructor
    · positivity
    · exact (div_le_one (by exact_mod_cast hk)).2 (by exact_mod_cast hi')

private theorem grid_zero (m k : ℕ) : (0 : ℝ) ∈ grid m k := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩

private theorem grid_one {m k : ℕ} (hm : 0 < m) : (1 : ℝ) ∈ grid m k := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨m, by simp, by simp [ne_of_gt hm]⟩

private theorem point_get {m k i : ℕ} (hi : i < (partitionKnots m k).length) :
    partitionPoint m k i = (partitionKnots m k).get ⟨i, hi⟩ := by
  exact List.getD_eq_get (partitionKnots m k) 0 ⟨i, hi⟩

private theorem point_mem {m k i : ℕ} (hi : i < (partitionKnots m k).length) :
    partitionPoint m k i ∈ grid m k := by
  rw [point_get hi]
  exact (Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)

private theorem point_index {m k : ℕ} {x : ℝ} (hx : x ∈ grid m k) :
    ∃ i, i < (partitionKnots m k).length ∧ partitionPoint m k i = x := by
  have hx' : x ∈ partitionKnots m k := (Finset.mem_sort (· ≤ ·)).mpr hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx'
  exact ⟨i.val, i.isLt, (point_get i.isLt).trans hi⟩

private theorem point_strict {m k i j : ℕ} (hij : i < j)
    (hj : j < (partitionKnots m k).length) :
    partitionPoint m k i < partitionPoint m k j := by
  have hi : i < (partitionKnots m k).length := hij.trans hj
  rw [point_get hi, point_get hj]
  exact (Finset.sortedLT_sort (grid m k)).strictMono_get
    (show (⟨i, hi⟩ : Fin (partitionKnots m k).length) < ⟨j, hj⟩ from hij)

private theorem point_mono {m k i j : ℕ} (hij : i ≤ j)
    (hj : j < (partitionKnots m k).length) :
    partitionPoint m k i ≤ partitionPoint m k j := by
  rcases hij.eq_or_lt with h | h
  · subst j
    exact le_rfl
  · exact (point_strict h hj).le

theorem endpoints {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    0 < partitionCells m k ∧
    partitionCells m k + 1 = (partitionKnots m k).length ∧
    partitionPoint m k 0 = 0 ∧ partitionPoint m k (partitionCells m k) = 1 := by
  obtain ⟨i0, hi0, h0⟩ := point_index (grid_zero m k)
  obtain ⟨i1, hi1, h1⟩ := point_index (grid_one (k := k) hm)
  have hne : i0 ≠ i1 := by
    intro heq
    subst i1
    linarith
  have hlen : 2 ≤ (partitionKnots m k).length := by omega
  have hP : partitionCells m k + 1 = (partitionKnots m k).length := by
    unfold partitionCells
    omega
  have hPlt : partitionCells m k < (partitionKnots m k).length := by omega
  have h0lt : 0 < (partitionKnots m k).length := by omega
  have hlow := (grid_bounds hm hk (point_mem h0lt)).1
  have hupp := (grid_bounds hm hk (point_mem hPlt)).2
  have h0le := point_mono (m := m) (k := k) (Nat.zero_le i0) hi0
  have h1le := point_mono (m := m) (k := k)
    (show i1 ≤ partitionCells m k by omega) hPlt
  refine ⟨by omega, hP, ?_, ?_⟩
  · linarith
  · linarith

end SAP.P022.WH.W1.P.T9_L1

open SAP.P022.WH.W1
open scoped BigOperators

theorem SAP.P022.WH.W1.T9_L1_proof : SAP.P022.WH.W1.T9_L1 := by
  classical
  intro m k hm hk
  have he := SAP.P022.WH.W1.P.T9_L1.endpoints
    (by omega : 0 < m) (by omega : 0 < k)
  rcases he with ⟨hPpos, hP, hfirst, hlast⟩
  have htelescope :
      (∑ r ∈ Finset.range (partitionCells m k),
        (codePoint m k (r + 1) - codePoint m k r)) =
        codePoint m k (partitionCells m k) - codePoint m k 0 := by
    simpa using (Finset.sum_range_sub (fun i : ℕ => codePoint m k i)
      (partitionCells m k))
  rw [htelescope]
  simp [codePoint, Nat.ne_of_gt hPpos, hlast]
  ring
