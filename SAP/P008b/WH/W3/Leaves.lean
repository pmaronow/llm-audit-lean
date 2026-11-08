import SAP.P008b.Defs.WholeW3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b.WH.W3

open scoped BigOperators

noncomputable section

/-- Closed, nonempty filled squares and their own/cross-polygon distances.
Prove closedness by continuous coordinate inequalities. For own distances,
the center itself (c=0), or the midpoint of the right side (c>0), attains the
upper bound. The first coordinate bounds every Euclidean distance below.
Metric.le_infDist then gives the lower bound. For cross distances, use the
20-unit separation, the half-side 1/8 and the largest offset 9/2 to obtain a
lower bound exceeding 5. The corrected editor's square_distances proof in
scratch/T16Corrected.lean and AronowAudit.P008.donut_spatial_distances give
the coordinate-bound route. This leaf is proved in Proofs.lean. -/
def T16_L1 : Prop :=
  (∀ i : Fin 2, (squarePolygonW3 i).Nonempty ∧ IsClosed (squarePolygonW3 i)) ∧
  (∀ i c, squareDistanceW3 i (i, c) = bufferCellDistance c) ∧
  (∀ i j c, i ≠ j → 5 < squareDistanceW3 i (j, c))

/-- Each square center is interior and has distance exactly 1/8 to its
nonempty topological boundary. Use the open strict coordinate inequalities
to prove interior membership. A frontier point has a coordinate at an endpoint
of the square, giving Euclidean distance at least 1/8 by PiLp.norm_apply_le.
The midpoint of the right side is a frontier point attaining the bound:
every ball about it contains a point just to its right, outside the square.
This is a boundary-distance identity, not a refutation of the corrected claim.
This leaf is proved in Proofs.lean. -/
def T16_L2 : Prop :=
  ∀ i : Fin 2,
    squareCellW3 i 0 ∈ interior (squarePolygonW3 i) ∧
    (frontier (squarePolygonW3 i)).Nonempty ∧
    Metric.infDist (squareCellW3 i 0) (frontier (squarePolygonW3 i)) = 1 / 8

/-- Assemble the corrected square/raster fixture. Only the two geometric
facts are leaves; raster membership, distinctness, finite selections, counts,
buffer-sum subtraction, all means and the Hajek contrasts are proved here. -/
theorem T16_assembly (h1 : T16_L1) (h2 : T16_L2) : T16WholeStatement_W3 := by
  classical
  rcases h1 with ⟨hclosed, hown, hcross⟩
  have hb (i : Fin 2) (r : ℝ) (hr : r ≤ 5) (j : Fin 2) (c : Fin 4) :
      squareDistanceW3 i (j, c) ≤ r ↔ j = i ∧ bufferCellDistance c ≤ r := by
    by_cases hij : i = j
    · subst j
      simp only [hown, true_and]
    · have hfar := hcross i j c hij
      have hnot : ¬ squareDistanceW3 i (j, c) ≤ r := by linarith
      simp [hnot, Ne.symm hij]
  have h₂ (i : Fin 2) : squareBufferW3 i 2 = {(i, 0)} := by
    ext ⟨j, c⟩
    simp only [squareBufferW3, Finset.mem_filter, Finset.mem_univ, true_and,
      hb i 2 (by norm_num)]
    fin_cases c <;> norm_num [bufferCellDistance, Prod.mk.injEq]
  have h₄ (i : Fin 2) : squareBufferW3 i 4 = {(i, 0), (i, 1), (i, 2)} := by
    ext ⟨j, c⟩
    simp only [squareBufferW3, Finset.mem_filter, Finset.mem_univ, true_and,
      hb i 4 (by norm_num)]
    fin_cases c <;> norm_num [bufferCellDistance, Prod.mk.injEq]
  have hcent (i : Fin 2) : squareCenteredW3 i = {(i, 2), (i, 3)} := by
    ext ⟨j, c⟩
    simp only [squareCenteredW3, Finset.mem_filter, Finset.mem_univ, true_and]
    norm_num only
    by_cases hij : i = j
    · subst j
      simp only [hown]
      fin_cases c <;> norm_num [bufferCellDistance, Prod.mk.injEq]
    · have hfar := hcross i j c hij
      simp [not_le_of_gt hfar, Ne.symm hij, Prod.mk.injEq]
  have hdiff (i : Fin 2) :
      squareBufferW3 i 4 \ squareBufferW3 i 2 = {(i, 1), (i, 2)} := by
    rw [h₂, h₄]
    norm_num [Finset.sdiff_eq_filter, Finset.filter_insert, Finset.filter_singleton]
  have hvalues (mode : Fin 3) (i : Fin 2) :
      squareMeansW3 mode i ![true, false] =
        if i = 0 then (![1, 4, 2] : Fin 3 → ℝ) mode else 0 := by
    unfold squareMeansW3
    rw [h₂, h₄, hcent]
    fin_cases mode <;> fin_cases i <;>
      norm_num [countMean, donutSpatialY, bufferCellOutcome, bit,
        Finset.sdiff_eq_filter, Finset.filter_insert, Finset.filter_singleton]
  have harch (i : Fin 2) (z : Assignment 2) :
      squareArchivedMeanW3 i 1 z = squareMeansW3 0 i z := by
    norm_num [squareArchivedMeanW3, squareRadiusW3, squareMeansW3, h₂, h₄,
      countMean, donutSpatialY, bufferCellOutcome,
      Finset.sdiff_eq_filter, Finset.filter_insert, Finset.filter_singleton]
  have hnt : nTreated ![true, false] = 1 := by
    simp only [nTreated, Fin.sum_univ_two]
    norm_num [bit]
  have hnc : nControl ![true, false] = 1 := by
    norm_num [nControl, hnt]
  have hstat (mode : Fin 3) : hajek (squareMeansW3 mode) ![true, false] =
      (![1, 4, 2] : Fin 3 → ℝ) mode := by
    norm_num [hajek, hnt, hnc, Fin.sum_univ_succ, bit, hvalues]
  have harchstat : hajek (fun i z => squareArchivedMeanW3 i 1 z) ![true, false] = 1 := by
    simpa only [harch, Matrix.cons_val_zero] using hstat 0
  refine ⟨?_, ?_, ?_, hown, hcross, ?_, ?_, ?_, ?_, ?_, harch, ?_, ?_,
    harchstat, hstat 1, hstat 2, ?_⟩
  · intro i
    exact ⟨(hclosed i).1, (hclosed i).2, (h2 i).1, (h2 i).2.1,
      (h2 i).2.2, by simpa [bufferCellDistance] using hown i 0⟩
  · intro ⟨i, c⟩ ⟨j, d⟩ heq
    have heq0 := congrArg (fun x : Plane => x 0) heq
    fin_cases i <;> fin_cases j <;> fin_cases c <;> fin_cases d <;>
      norm_num [squareCellW3, squareOffsetW3, PiLp.toLp_apply] at heq0
    all_goals rfl
  · intro i c
    refine ⟨40 * (i.val : ℤ) + (![0, 5, 7, 9] : Fin 4 → ℤ) c, 0, ?_⟩
    fin_cases i <;> fin_cases c <;>
      norm_num [squareCellW3, squareOffsetW3]
  · intro c
    norm_num [donutSpatialY, bit]
  · exact ⟨hnt, hnc⟩
  · intro i
    refine ⟨h₂ i, h₄ i, hdiff i, ?_, hcent i⟩
    ext ic
    simp only [squareBufferW3, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and, not_le]
    exact and_comm
  · intro i
    rw [hdiff, h₂, h₄, hcent]
    norm_num
  · rw [h₂, h₄]
    norm_num [donutSpatialY, bufferCellOutcome, bit]
  · intro mode
    simp [hvalues]
  · intro i
    simp [harch, hvalues]
  · rw [harchstat, hstat]
    norm_num

end

end SAP.P008b.WH.W3
