import SAP.P008b.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b.WH.W3.P.T16_L1

open scoped BigOperators

noncomputable section

theorem square_nonempty (i : Fin 2) :
    (SAP.P008b.squarePolygonW3 i).Nonempty := by
  refine ⟨SAP.P008b.squareCellW3 i 0, ?_⟩
  norm_num [SAP.P008b.squarePolygonW3, SAP.P008b.squareCellW3,
    SAP.P008b.squareOffsetW3, PiLp.toLp_apply]

theorem square_closed (i : Fin 2) :
    IsClosed (SAP.P008b.squarePolygonW3 i) := by
  have h0 : Continuous (fun x : SAP.P008b.Plane => x 0) := by fun_prop
  have h1 : Continuous (fun x : SAP.P008b.Plane => x 1) := by fun_prop
  exact (isClosed_le continuous_const h0).inter
    ((isClosed_le h0 continuous_const).inter
      ((isClosed_le continuous_const h1).inter (isClosed_le h1 continuous_const)))

/-- A coordinate difference is a lower bound for Euclidean distance. -/
theorem coord_bound (u v : SAP.P008b.Plane) (k : Fin 2) :
    |u k - v k| ≤ dist u v := by
  simpa only [dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs] using
    PiLp.norm_apply_le (u - v) k

end

end SAP.P008b.WH.W3.P.T16_L1

open SAP.P008b.WH.W3.P.T16_L1

/-- Exact own-square distances and strict separation from the other square. -/
theorem SAP.P008b.WH.W3.T16_L1_proof : SAP.P008b.WH.W3.T16_L1 := by
  refine ⟨fun i => ⟨square_nonempty i, square_closed i⟩, ?_, ?_⟩
  · intro i c
    let q : SAP.P008b.Plane := WithLp.toLp 2
      ![20 * (i : ℝ) + (if c = 0 then 0 else 1 / 8), 0]
    have hq : q ∈ SAP.P008b.squarePolygonW3 i := by
      fin_cases c <;>
        norm_num [SAP.P008b.squarePolygonW3, q, PiLp.toLp_apply] <;> linarith
    have hd : 0 ≤ SAP.P008b.bufferCellDistance c := by
      fin_cases c <;> norm_num [SAP.P008b.bufferCellDistance]
    have he : dist (SAP.P008b.squareCellW3 i c) q =
        SAP.P008b.bufferCellDistance c := by
      have hs : dist (SAP.P008b.squareCellW3 i c) q ^ 2 =
          SAP.P008b.bufferCellDistance c ^ 2 := by
        rw [EuclideanSpace.dist_sq_eq]
        fin_cases c <;>
          norm_num [SAP.P008b.squareCellW3, q,
            SAP.P008b.squareOffsetW3,
            SAP.P008b.bufferCellDistance,
            Fin.sum_univ_succ, Real.dist_eq, sq_abs]
      nlinarith [dist_nonneg (x := SAP.P008b.squareCellW3 i c) (y := q)]
    apply le_antisymm
    · exact (Metric.infDist_le_dist_of_mem hq).trans_eq he
    · apply (Metric.le_infDist (square_nonempty i)).mpr
      intro x hx
      have hb := hx.2.1
      have hc := coord_bound (SAP.P008b.squareCellW3 i c) x 0
      simp only [SAP.P008b.squareCellW3, PiLp.toLp_apply,
        Matrix.cons_val_zero] at hc
      have ha := (abs_le.mp hc).2
      fin_cases c
      · simp [SAP.P008b.bufferCellDistance]
      all_goals
        norm_num [SAP.P008b.bufferCellDistance,
          SAP.P008b.squareOffsetW3,
          SAP.P008b.squareCellW3] at ha ⊢
        linarith
  · intro i j c hij
    have hlower : 6 ≤ SAP.P008b.squareDistanceW3 i (j, c) := by
      apply (Metric.le_infDist (square_nonempty i)).mpr
      intro x hx
      have hb0 := hx.1
      have hb1 := hx.2.1
      have hc := coord_bound (SAP.P008b.squareCellW3 j c) x 0
      simp only [SAP.P008b.squareCellW3, PiLp.toLp_apply,
        Matrix.cons_val_zero] at hc
      have ha := abs_le.mp hc
      fin_cases i <;> fin_cases j <;> norm_num at hij <;>
        fin_cases c <;>
          norm_num [SAP.P008b.squareCellW3,
            SAP.P008b.squareOffsetW3] at ha hb0 hb1 ⊢ <;>
            linarith
    linarith
