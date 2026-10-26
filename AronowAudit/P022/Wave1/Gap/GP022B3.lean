import AronowAudit.P022.P022_Variance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD



namespace AronowAudit.P022.Wave1

open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
set_option autoImplicit false

noncomputable section



/-! ## P022-T9: union-grid geometry and cell ranks -/

private def T9_grid (m k : ℕ) : Finset ℝ :=
  ((Finset.range (m + 1)).image (fun i : ℕ => (i : ℝ) / m)) ∪
    ((Finset.range (k + 1)).image (fun j : ℕ => (j : ℝ) / k))

private theorem T9_grid_bounds {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    {x : ℝ} (hx : x ∈ T9_grid m k) : 0 ≤ x ∧ x ≤ 1 := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    constructor
    · positivity
    · exact (div_le_one (by exact_mod_cast hm)).2 (by exact_mod_cast hi')
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    constructor
    · positivity
    · exact (div_le_one (by exact_mod_cast hk)).2 (by exact_mod_cast hi')

private theorem T9_grid_zero (m k : ℕ) : (0 : ℝ) ∈ T9_grid m k := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩

private theorem T9_grid_one {m k : ℕ} (hm : 0 < m) : (1 : ℝ) ∈ T9_grid m k := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨m, by simp, by simp [ne_of_gt hm]⟩

private theorem T9_point_get {m k i : ℕ} (hi : i < (partitionKnots m k).length) :
    partitionPoint m k i = (partitionKnots m k).get ⟨i, hi⟩ := by
  exact List.getD_eq_get (partitionKnots m k) 0 ⟨i, hi⟩

private theorem T9_point_mem {m k i : ℕ} (hi : i < (partitionKnots m k).length) :
    partitionPoint m k i ∈ T9_grid m k := by
  rw [T9_point_get hi]
  exact (Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)

private theorem T9_point_index {m k : ℕ} {x : ℝ} (hx : x ∈ T9_grid m k) :
    ∃ i, i < (partitionKnots m k).length ∧ partitionPoint m k i = x := by
  have hx' : x ∈ partitionKnots m k := (Finset.mem_sort (· ≤ ·)).mpr hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx'
  exact ⟨i.val, i.isLt, (T9_point_get i.isLt).trans hi⟩

private theorem T9_point_strict {m k i j : ℕ} (hij : i < j)
    (hj : j < (partitionKnots m k).length) :
    partitionPoint m k i < partitionPoint m k j := by
  have hi : i < (partitionKnots m k).length := hij.trans hj
  rw [T9_point_get hi, T9_point_get hj]
  exact (Finset.sortedLT_sort (T9_grid m k)).strictMono_get
    (show (⟨i, hi⟩ : Fin (partitionKnots m k).length) < ⟨j, hj⟩ from hij)

private theorem T9_point_mono {m k i j : ℕ} (hij : i ≤ j)
    (hj : j < (partitionKnots m k).length) :
    partitionPoint m k i ≤ partitionPoint m k j := by
  rcases hij.eq_or_lt with h | h
  · subst j; exact le_rfl
  · exact (T9_point_strict h hj).le

private theorem T9_endpoints {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    0 < partitionCells m k ∧
    partitionCells m k + 1 = (partitionKnots m k).length ∧
    partitionPoint m k 0 = 0 ∧ partitionPoint m k (partitionCells m k) = 1 := by
  obtain ⟨i0, hi0, h0⟩ := T9_point_index (T9_grid_zero m k)
  obtain ⟨i1, hi1, h1⟩ := T9_point_index (T9_grid_one (k := k) hm)
  have hne : i0 ≠ i1 := by intro heq; subst i1; linarith
  have hlen : 2 ≤ (partitionKnots m k).length := by omega
  have hP : partitionCells m k + 1 = (partitionKnots m k).length := by
    unfold partitionCells
    omega
  have hPlt : partitionCells m k < (partitionKnots m k).length := by omega
  have h0lt : 0 < (partitionKnots m k).length := by omega
  have hlow := (T9_grid_bounds hm hk (T9_point_mem h0lt)).1
  have hupp := (T9_grid_bounds hm hk (T9_point_mem hPlt)).2
  have h0le := T9_point_mono (m := m) (k := k) (Nat.zero_le i0) hi0
  have h1le := T9_point_mono (m := m) (k := k)
    (show i1 ≤ partitionCells m k by omega) hPlt
  refine ⟨by omega, hP, ?_, ?_⟩
  · linarith
  · linarith

private theorem T9_no_interior_knot {m k r : ℕ}
    (hr : r < partitionCells m k) {x : ℝ} (hx : x ∈ T9_grid m k) :
    ¬ (partitionPoint m k r < x ∧ x < partitionPoint m k (r + 1)) := by
  obtain ⟨i, hi, hix⟩ := T9_point_index hx
  have hright : r + 1 < (partitionKnots m k).length := by
    unfold partitionCells at hr
    omega
  intro h
  by_cases hir : i ≤ r
  · have hh := T9_point_mono (m := m) (k := k) hir (by omega)
    linarith
  · have hh := T9_point_mono (m := m) (k := k) (show r + 1 ≤ i by omega) hi
    linarith

private theorem T9_cell_bounds {m k r : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hr : r < partitionCells m k) {u : ℝ}
    (hu : partitionPoint m k r < u ∧ u < partitionPoint m k (r + 1)) :
    0 < u ∧ u < 1 := by
  have hl : r < (partitionKnots m k).length := by unfold partitionCells at hr; omega
  have hh : r + 1 < (partitionKnots m k).length := by unfold partitionCells at hr; omega
  have h0 := (T9_grid_bounds hm hk (T9_point_mem hl)).1
  have h1 := (T9_grid_bounds hm hk (T9_point_mem hh)).2
  constructor <;> linarith [hu.1, hu.2]

private theorem T9_rank_grid {m k s : ℕ} (hs : s = m ∨ s = k)
    (j : ℕ) (hj : j ≤ s) : (j : ℝ) / s ∈ T9_grid m k := by
  rcases hs with rfl | rfl
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩

private theorem T9_ceil_cell {m k s r : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hs : s = m ∨ s = k) (hr : r < partitionCells m k) {u v : ℝ}
    (hu : partitionPoint m k r < u ∧ u < partitionPoint m k (r + 1))
    (hv : partitionPoint m k r < v ∧ v < partitionPoint m k (r + 1)) :
    Nat.ceil ((s : ℝ) * u) = Nat.ceil ((s : ℝ) * v) := by
  have hsN : 0 < s := by rcases hs with rfl | rfl <;> assumption
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hsN
  have hu01 := T9_cell_bounds hm hk hr hu
  have hv01 := T9_cell_bounds hm hk hr hv
  have hdir : ∀ {x y : ℝ},
      partitionPoint m k r < x ∧ x < partitionPoint m k (r + 1) →
      partitionPoint m k r < y ∧ y < partitionPoint m k (r + 1) →
      x < 1 → y < 1 → Nat.ceil ((s : ℝ) * x) ≤ Nat.ceil ((s : ℝ) * y) := by
    intro x y hx hy hx1 hy1
    by_contra hnle
    have hlt : Nat.ceil ((s : ℝ) * y) < Nat.ceil ((s : ℝ) * x) := by omega
    let j := Nat.ceil ((s : ℝ) * y)
    have hj : j ≤ s := Nat.ceil_le.mpr (by
      have hh := mul_lt_mul_of_pos_left hy1 hsR
      nlinarith [hh])
    have hleft : partitionPoint m k r < (j : ℝ) / s := by
      have hle : y ≤ (j : ℝ) / s := (le_div_iff₀ hsR).2 (by
        nlinarith [Nat.le_ceil ((s : ℝ) * y)])
      exact hy.1.trans_le hle
    have hright : (j : ℝ) / s < partitionPoint m k (r + 1) := by
      have hlt' : (j : ℝ) < (s : ℝ) * x := Nat.lt_ceil.mp hlt
      have hlt'' : (j : ℝ) / s < x := (div_lt_iff₀ hsR).2 (by nlinarith)
      exact hlt''.trans hx.2
    exact T9_no_interior_knot hr (T9_rank_grid hs j hj) ⟨hleft, hright⟩
  exact le_antisymm (hdir hu hv hu01.2 hv01.2) (hdir hv hu hv01.2 hu01.2)

private theorem T9_reflected_rank {m k s r : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hs : s = m ∨ s = k) (hr : r < partitionCells m k) {u : ℝ}
    (hu : partitionPoint m k r < u ∧ u < partitionPoint m k (r + 1)) :
    Nat.ceil ((s : ℝ) * (1 - u)) = s + 1 - Nat.ceil ((s : ℝ) * u) := by
  have hsN : 0 < s := by rcases hs with rfl | rfl <;> assumption
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hsN
  have hu01 := T9_cell_bounds hm hk hr hu
  let j := Nat.ceil ((s : ℝ) * u)
  have hjpos : 0 < j := Nat.one_le_ceil_iff.mpr (mul_pos hsR hu01.1)
  have hjle : j ≤ s := Nat.ceil_le.mpr (by
    have hh := mul_lt_mul_of_pos_left hu01.2 hsR
    nlinarith [hh])
  have hjspec : ((j - 1 : ℕ) : ℝ) < (s : ℝ) * u ∧ (s : ℝ) * u ≤ (j : ℝ) :=
    (Nat.ceil_eq_iff (by omega : j ≠ 0)).mp rfl
  have hstrict : (s : ℝ) * u < (j : ℝ) := by
    apply lt_of_le_of_ne hjspec.2
    intro heq
    have huj : (j : ℝ) / s = u := (div_eq_iff hsR.ne').2 (by nlinarith [heq])
    exact T9_no_interior_knot hr (T9_rank_grid hs j hjle) (by simpa [huj] using hu)
  have hcastj : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ j)]; norm_num
  have hcastl : ((s + 1 - j : ℕ) : ℝ) = (s : ℝ) + 1 - j := by
    rw [Nat.cast_sub (by omega : j ≤ s + 1)]; push_cast; rfl
  have hcastlm : (((s + 1 - j) - 1 : ℕ) : ℝ) = (s : ℝ) - j := by
    rw [Nat.cast_sub (by omega : 1 ≤ s + 1 - j), hcastl]
    push_cast
    ring
  apply (Nat.ceil_eq_iff (by omega : s + 1 - j ≠ 0)).2
  rw [hcastlm, hcastl]
  constructor <;> nlinarith [hjspec.1]

private theorem T9_first_rank {m k s : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hs : s = m ∨ s = k) {u : ℝ}
    (hu : partitionPoint m k 0 < u ∧ u < partitionPoint m k 1) :
    Nat.ceil ((s : ℝ) * u) = 1 := by
  have he := T9_endpoints hm hk
  have hsN : 0 < s := by rcases hs with rfl | rfl <;> assumption
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hsN
  have hu0 : 0 < u := by rw [he.2.2.1] at hu; exact hu.1
  have hp : partitionPoint m k 1 ≤ (1 : ℝ) / s := by
    by_contra hh
    have hlt : (1 : ℝ) / s < partitionPoint m k 1 := lt_of_not_ge hh
    exact T9_no_interior_knot he.1 (T9_rank_grid hs 1 (by omega))
      ⟨by rw [he.2.2.1]; positivity, by simpa only [Nat.cast_one, Nat.zero_add] using hlt⟩
  apply (Nat.ceil_eq_iff (by decide : (1 : ℕ) ≠ 0)).2
  norm_num
  constructor
  · positivity
  · have hu1 : u < 1 / (s : ℝ) := hu.2.trans_le hp
    have hh := (lt_div_iff₀ hsR).1 hu1
    nlinarith

private theorem T9_code_inside {m k r : ℕ}
    (hr : r < partitionCells m k)
    (hw : 2 * codeEpsilon < cellWidth m k r) :
    partitionPoint m k r < codePoint m k (r + 1) ∧
      codePoint m k (r + 1) < partitionPoint m k (r + 1) := by
  have he : 0 < codeEpsilon := by norm_num [codeEpsilon]
  simp only [codePoint, Nat.succ_ne_zero, if_false]
  unfold cellWidth at hw
  constructor <;> linarith

private def T9_codeProduct {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (B : BoundSide) (r : ℕ) : ℝ :=
  empiricalQuantile a (codePoint m k (r + 1)) *
    (if B = .H then orderStatistic b (Nat.ceil ((k : ℝ) * codePoint m k (r + 1)))
     else orderStatistic b (k + 1 - Nat.ceil ((k : ℝ) * codePoint m k (r + 1))))

private theorem T9_product_cell {m k r : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide)
    (hr : r < partitionCells m k) (hw : 2 * codeEpsilon < cellWidth m k r)
    {u : ℝ} (hu : partitionPoint m k r < u ∧ u < partitionPoint m k (r + 1)) :
    empiricalQuantile a u * empiricalQuantile b (if B = .H then u else 1 - u) =
      T9_codeProduct a b B r := by
  have hq := T9_code_inside hr hw
  have hma := T9_ceil_cell hm hk (Or.inl rfl) hr hu hq
  have hkb := T9_ceil_cell hm hk (Or.inr rfl) hr hu hq
  cases B with
  | H =>
    simp only [T9_codeProduct, if_pos rfl, ite_true, empiricalQuantile]
    rw [hma, hkb]
  | L =>
    have href := T9_reflected_rank hm hk (Or.inr rfl) hr hu
    simp only [T9_codeProduct, reduceCtorEq, if_false, empiricalQuantile]
    rw [hma, href, hkb]

/-- Direct raw-product quadrature for the Appendix B integration argument. -/
private theorem T9_raw_quadrature {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide)
    (hw : ∀ r < partitionCells m k, 2 * codeEpsilon < cellWidth m k r) :
    (∫ u in (0 : ℝ)..1, empiricalQuantile a u *
      empiricalQuantile b (if B = .H then u else 1 - u)) =
      ∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r * T9_codeProduct a b B r := by
  let f : ℝ → ℝ := fun u => empiricalQuantile a u *
    empiricalQuantile b (if B = .H then u else 1 - u)
  have he := T9_endpoints hm hk
  have hcell : ∀ r < partitionCells m k, ∀ u ∈
      Set.Ioo (partitionPoint m k r) (partitionPoint m k (r + 1)),
      f u = T9_codeProduct a b B r := by
    intro r hr u hu
    exact T9_product_cell hm hk a b B hr (hw r hr) hu
  have hpr : ∀ r < partitionCells m k,
      partitionPoint m k r ≤ partitionPoint m k (r + 1) := by
    intro r hr
    apply (T9_point_strict (Nat.lt_succ_self r) (by omega)).le
  have hint : ∀ r < partitionCells m k, IntervalIntegrable f volume
      (partitionPoint m k r) (partitionPoint m k (r + 1)) := by
    intro r hr
    apply (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => T9_codeProduct a b B r) volume
        (partitionPoint m k r) (partitionPoint m k (r + 1))).congr_uIoo
    rw [Set.uIoo_of_le (hpr r hr)]
    intro u hu
    exact (hcell r hr u hu).symm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := partitionPoint m k) hint
  rw [he.2.2.1, he.2.2.2] at hsum
  calc
    (∫ u in (0 : ℝ)..1, empiricalQuantile a u *
      empiricalQuantile b (if B = .H then u else 1 - u)) =
        ∑ r ∈ Finset.range (partitionCells m k), ∫ u in
          (partitionPoint m k r)..(partitionPoint m k (r + 1)), f u := hsum.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr' : r < partitionCells m k := Finset.mem_range.mp hr
      calc
        (∫ u in (partitionPoint m k r)..(partitionPoint m k (r + 1)), f u) =
            ∫ _u in (partitionPoint m k r)..(partitionPoint m k (r + 1)),
              T9_codeProduct a b B r :=
          intervalIntegral.integral_congr_Ioo_of_le (hpr r hr') (hcell r hr')
        _ = cellWidth m k r * T9_codeProduct a b B r := by
          simp only [intervalIntegral.integral_const, smul_eq_mul, cellWidth]

private theorem T9_weight_difference {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (r : ℕ) :
    codePoint m k (r + 1) - codePoint m k r =
      cellWidth m k r - (if r = 0 then 2 * codeEpsilon else 0) := by
  have hzero := (T9_endpoints hm hk).2.2.1
  by_cases hr : r = 0
  · subst r
    simp only [codePoint, Nat.succ_ne_zero, if_false, if_pos rfl, ite_true, cellWidth, hzero]
    ring
  · simp only [codePoint, Nat.succ_ne_zero, if_false, if_neg hr, cellWidth]
    ring

private theorem T9_first_product {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide)
    (hw : ∀ r < partitionCells m k, 2 * codeEpsilon < cellWidth m k r) :
    T9_codeProduct a b B 0 =
      orderStatistic a 1 * orderStatistic b (if B = .H then 1 else k) := by
  have hP := (T9_endpoints hm hk).1
  have hq := T9_code_inside hP (hw 0 hP)
  have hma := T9_first_rank hm hk (Or.inl rfl) hq
  have hkb := T9_first_rank hm hk (Or.inr rfl) hq
  cases B <;> simp only [T9_codeProduct, empiricalQuantile, hma, hkb,
    reduceCtorEq, if_true, if_false, Nat.add_sub_cancel]

/-- Only the first weight changes; no rounded-number semantics is used. -/
private theorem T9_raw_sum_discrepancy {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide)
    (hw : ∀ r < partitionCells m k, 2 * codeEpsilon < cellWidth m k r) :
    (∑ r ∈ Finset.range (partitionCells m k),
      (codePoint m k (r + 1) - codePoint m k r) *
      empiricalQuantile a (codePoint m k (r + 1)) *
      (if B = .H then orderStatistic b (Nat.ceil ((k : ℝ) * codePoint m k (r + 1)))
       else orderStatistic b (k + 1 - Nat.ceil ((k : ℝ) * codePoint m k (r + 1))))) =
    (∫ u in (0 : ℝ)..1, empiricalQuantile a u *
      empiricalQuantile b (if B = .H then u else 1 - u)) -
      2 * codeEpsilon * orderStatistic a 1 * orderStatistic b (if B = .H then 1 else k) := by
  classical
  rw [T9_raw_quadrature hm hk a b B hw]
  have hP := (T9_endpoints hm hk).1
  calc
    _ = ∑ r ∈ Finset.range (partitionCells m k),
        (cellWidth m k r * T9_codeProduct a b B r -
          if r = 0 then 2 * codeEpsilon * T9_codeProduct a b B 0 else 0) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [T9_weight_difference hm hk]
      by_cases hr : r = 0
      · subst r
        simp only [if_pos rfl, ite_true, T9_codeProduct]
        ring
      · simp only [if_neg hr, sub_zero, T9_codeProduct]
        ring
    _ = (∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r * T9_codeProduct a b B r) -
        2 * codeEpsilon * T9_codeProduct a b B 0 := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_range, hP, if_true]
    _ = _ := by rw [T9_first_product hm hk a b B hw]; ring

theorem appendixB_general_discrepancy_proof {N m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (hN : m + k ≤ N) (a : Fin m → ℝ) (b : Fin k → ℝ)
    (hw : ∀ r < partitionCells m k, 2 * codeEpsilon < cellWidth m k r) :
    printedCodeBound N a b .H - estimateBound N a b .H =
      -4 * codeEpsilon * orderStatistic a 1 * orderStatistic b 1 / ((N : ℝ) - 1) ∧
    printedCodeBound N a b .L - estimateBound N a b .L =
      -4 * codeEpsilon * orderStatistic a 1 * orderStatistic b k / ((N : ℝ) - 1) := by
  have hm0 : 0 < m := by omega
  have hk0 : 0 < k := by omega
  have hrawH := T9_raw_sum_discrepancy hm0 hk0 a b .H hw
  have hrawL := T9_raw_sum_discrepancy hm0 hk0 a b .L hw
  constructor
  · unfold printedCodeBound estimateBound
    rw [hrawH]
    simp only [sharpCovariance, varianceExpression, if_pos rfl, ite_true, div_eq_mul_inv]
    ring
  · unfold printedCodeBound estimateBound
    rw [hrawL]
    simp only [sharpCovariance, varianceExpression, reduceCtorEq, if_false, div_eq_mul_inv]
    ring

end

end AronowAudit.P022.Wave1
