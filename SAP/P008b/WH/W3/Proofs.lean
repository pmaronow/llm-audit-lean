import SAP.P008b.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b.WH.W3

open scoped BigOperators

noncomputable section

theorem square_nonempty (i : Fin 2) : (squarePolygonW3 i).Nonempty := by
  refine ⟨squareCellW3 i 0, ?_⟩
  norm_num [squarePolygonW3, squareCellW3, squareOffsetW3, PiLp.toLp_apply]

theorem square_closed (i : Fin 2) : IsClosed (squarePolygonW3 i) := by
  have h0 : Continuous (fun x : Plane => x 0) := by fun_prop
  have h1 : Continuous (fun x : Plane => x 1) := by fun_prop
  exact (isClosed_le continuous_const h0).inter
    ((isClosed_le h0 continuous_const).inter
      ((isClosed_le continuous_const h1).inter (isClosed_le h1 continuous_const)))

/-- Euclidean coordinate distances are lower bounds for Euclidean distance. -/
theorem coord_bound (u v : Plane) (k : Fin 2) : |u k - v k| ≤ dist u v := by
  simpa only [dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs] using
    PiLp.norm_apply_le (u - v) k

/-- Exact distances to the corrected filled squares. Adapted from the corrected
editor's square_distances proof, without importing the old rectangle witness. -/
theorem T16_L1_proof : T16_L1 := by
  refine ⟨fun i => ⟨square_nonempty i, square_closed i⟩, ?_, ?_⟩
  · intro i c
    let q : Plane := WithLp.toLp 2
      ![20 * (i : ℝ) + (if c = 0 then 0 else 1 / 8), 0]
    have hq : q ∈ squarePolygonW3 i := by
      fin_cases c <;> norm_num [squarePolygonW3, q, PiLp.toLp_apply] <;> linarith
    have hd : 0 ≤ bufferCellDistance c := by
      fin_cases c <;> norm_num [bufferCellDistance]
    have he : dist (squareCellW3 i c) q = bufferCellDistance c := by
      have hs : dist (squareCellW3 i c) q ^ 2 = bufferCellDistance c ^ 2 := by
        rw [EuclideanSpace.dist_sq_eq]
        fin_cases c <;>
          norm_num [squareCellW3, q, squareOffsetW3, bufferCellDistance,
            Fin.sum_univ_succ, Real.dist_eq, sq_abs]
      nlinarith [dist_nonneg (x := squareCellW3 i c) (y := q)]
    apply le_antisymm
    · exact (Metric.infDist_le_dist_of_mem hq).trans_eq he
    · apply (Metric.le_infDist (square_nonempty i)).mpr
      intro x hx
      have hb := hx.2.1
      have hc := coord_bound (squareCellW3 i c) x 0
      simp only [squareCellW3, PiLp.toLp_apply, Matrix.cons_val_zero] at hc
      have ha := (abs_le.mp hc).2
      fin_cases c
      · simp [bufferCellDistance]
      all_goals
        norm_num [bufferCellDistance, squareOffsetW3, squareCellW3] at ha ⊢
        linarith
  · intro i j c hij
    have hlower : 6 ≤ squareDistanceW3 i (j, c) := by
      apply (Metric.le_infDist (square_nonempty i)).mpr
      intro x hx
      have hb0 := hx.1
      have hb1 := hx.2.1
      have hc := coord_bound (squareCellW3 j c) x 0
      simp only [squareCellW3, PiLp.toLp_apply, Matrix.cons_val_zero] at hc
      have ha := abs_le.mp hc
      fin_cases i <;> fin_cases j <;> norm_num at hij <;>
        fin_cases c <;> norm_num [squareCellW3, squareOffsetW3] at ha hb0 hb1 ⊢ <;>
        linarith
    linarith

/-- The center-to-boundary identity in the corrected definitions. The strict
square is open, and the right-side midpoint is an attained nearest boundary
point. No zero-boundary-distance assertion is used. -/
theorem T16_L2_proof : T16_L2 := by
  intro i
  let c : ℝ := 20 * (i : ℝ)
  let strictSquare : Set Plane :=
    {x | |x 0 - c| < (1 / 8 : ℝ) ∧ |x 1| < (1 / 8 : ℝ)}
  have hopen : IsOpen strictSquare := by
    have h0 : Continuous fun x : Plane => |x 0 - c| := by fun_prop
    have h1 : Continuous fun x : Plane => |x 1| := by fun_prop
    exact (isOpen_lt h0 continuous_const).inter (isOpen_lt h1 continuous_const)
  have hsub : strictSquare ⊆ squarePolygonW3 i := by
    intro x hx
    rcases abs_lt.mp hx.1 with ⟨h0, h1⟩
    rcases abs_lt.mp hx.2 with ⟨h2, h3⟩
    change c - 1 / 8 ≤ x 0 ∧ x 0 ≤ c + 1 / 8 ∧ -1 / 8 ≤ x 1 ∧ x 1 ≤ 1 / 8
    exact ⟨by linarith, by linarith, by linarith, h3.le⟩
  have hint : strictSquare ⊆ interior (squarePolygonW3 i) :=
    (subset_interior_iff_isOpen.mpr hopen).trans (interior_mono hsub)
  have hcenter : squareCellW3 i 0 ∈ interior (squarePolygonW3 i) := by
    apply hint
    norm_num [strictSquare, squareCellW3, squareOffsetW3, c, PiLp.toLp_apply]
  let q : Plane := WithLp.toLp 2 ![c + (1 / 8 : ℝ), 0]
  have hqmem : q ∈ squarePolygonW3 i := by
    norm_num [q, squarePolygonW3, c, PiLp.toLp_apply]
    linarith
  have hqnot : q ∉ interior (squarePolygonW3 i) := by
    intro hqi
    obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp isOpen_interior) q hqi
    let y : Plane := WithLp.toLp 2 ![c + (1 / 8 : ℝ) + ε / 2, 0]
    have hydist : dist q y = ε / 2 := by
      apply (sq_eq_sq₀ dist_nonneg (by positivity)).mp
      rw [EuclideanSpace.dist_sq_eq]
      norm_num [q, y, PiLp.toLp_apply, abs_of_pos hε]
    have hyball : y ∈ Metric.ball q ε := by
      rw [Metric.mem_ball, dist_comm, hydist]
      linarith
    have hys := interior_subset (hball hyball)
    have hfirst : c + (1 / 8 : ℝ) + ε / 2 ≤ c + 1 / 8 := hys.2.1
    linarith
  have hqfront : q ∈ frontier (squarePolygonW3 i) := by
    rw [(square_closed i).frontier_eq]
    exact ⟨hqmem, hqnot⟩
  have hqdist : dist (squareCellW3 i 0) q = (1 / 8 : ℝ) := by
    apply (sq_eq_sq₀ dist_nonneg (by norm_num)).mp
    rw [EuclideanSpace.dist_sq_eq]
    norm_num [squareCellW3, squareOffsetW3, q, c, PiLp.toLp_apply]
  have hside (x : Plane) (hx : x ∈ frontier (squarePolygonW3 i)) :
      |x 0 - c| = (1 / 8 : ℝ) ∨ |x 1| = (1 / 8 : ℝ) := by
    rw [(square_closed i).frontier_eq] at hx
    have h0 : |x 0 - c| ≤ (1 / 8 : ℝ) := by
      apply abs_le.mpr
      have hlo : c - 1 / 8 ≤ x 0 := hx.1.1
      have hhi : x 0 ≤ c + 1 / 8 := hx.1.2.1
      constructor <;> linarith
    have h1 : |x 1| ≤ (1 / 8 : ℝ) :=
      abs_le.mpr ⟨by linarith [hx.1.2.2.1], hx.1.2.2.2⟩
    by_contra hnot
    push Not at hnot
    have hxstrict : x ∈ strictSquare :=
      ⟨lt_of_le_of_ne h0 hnot.1, lt_of_le_of_ne h1 hnot.2⟩
    exact hx.2 (hint hxstrict)
  have hlower : (1 / 8 : ℝ) ≤
      Metric.infDist (squareCellW3 i 0) (frontier (squarePolygonW3 i)) := by
    apply (Metric.le_infDist ⟨q, hqfront⟩).mpr
    intro x hx
    rcases hside x hx with h0 | h1
    · have hn : |x 0 - c| ≤ dist x (squareCellW3 i 0) := by
        simpa [squareCellW3, squareOffsetW3, c, PiLp.toLp_apply] using
          coord_bound x (squareCellW3 i 0) 0
      rw [h0, dist_comm] at hn
      exact hn
    · have hn := coord_bound x (squareCellW3 i 0) 1
      simpa [squareCellW3, PiLp.toLp_apply, h1, dist_comm] using hn
  have hupper : Metric.infDist (squareCellW3 i 0) (frontier (squarePolygonW3 i)) ≤
      (1 / 8 : ℝ) := (Metric.infDist_le_dist_of_mem hqfront).trans_eq hqdist
  exact ⟨hcenter, ⟨q, hqfront⟩, le_antisymm hupper hlower⟩

/-- The corrected canonical claim, with both geometric leaves discharged. -/
theorem T16_whole : T16WholeStatement_W3 :=
  T16_assembly T16_L1_proof T16_L2_proof

end

end SAP.P008b.WH.W3
