import SAP.P008b.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b.WH.W3.P.T16_L2

open scoped BigOperators

noncomputable section

theorem square_closed (i : Fin 2) : IsClosed (squarePolygonW3 i) := by
  have h0 : Continuous (fun x : Plane => x 0) := by fun_prop
  have h1 : Continuous (fun x : Plane => x 1) := by fun_prop
  exact (isClosed_le continuous_const h0).inter
    ((isClosed_le h0 continuous_const).inter
      ((isClosed_le continuous_const h1).inter (isClosed_le h1 continuous_const)))

theorem coord_bound (u v : Plane) (k : Fin 2) : |u k - v k| ≤ dist u v := by
  simpa only [dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs] using
    PiLp.norm_apply_le (u - v) k

end

end SAP.P008b.WH.W3.P.T16_L2

open SAP.P008b.WH.W3.P.T16_L2

noncomputable section

theorem SAP.P008b.WH.W3.T16_L2_proof : SAP.P008b.WH.W3.T16_L2 := by
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
