import SAP.P004b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2.P.T16_L1

open scoped BigOperators Classical Topology

private lemma vertical_gap_le_dist (x y : EuclideanSpace ℝ (Fin 2))
    (hxy : x 1 ≤ y 1) : y 1 - x 1 ≤ dist x y := by
  have hsq := AronowAudit.P004.Wave1.spacing_dist_sq x y
  have hdist : 0 ≤ dist x y := dist_nonneg
  have hgap : 0 ≤ y 1 - x 1 := sub_nonneg.mpr hxy
  nlinarith [sq_nonneg (dist x y - (y 1 - x 1))]

private lemma vertical_projection_dist (x : EuclideanSpace ℝ (Fin 2)) :
    dist x (planePoint (x 0) 2) = |x 1 - 2| := by
  simp [EuclideanSpace.dist_eq, planePoint, Fin.sum_univ_succ, Real.dist_eq,
    Real.sqrt_sq_eq_abs]

end SAP.P004b.WH.W2.P.T16_L1

theorem SAP.P004b.WH.W2.T16_L1_proof : SAP.P004b.WH.W2.T16_L1 := by
  intro L hL x hx
  have hcoords : 0 ≤ x 0 ∧ x 0 ≤ L + 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 := by
    rcases hx with hx | hx
    · change 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 at hx
      exact ⟨hx.1, by linarith, hx.2.2.1, hx.2.2.2⟩
    · change L ≤ x 0 ∧ x 0 ≤ L + 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 at hx
      exact ⟨by linarith, hx.2.1, hx.2.2.1, hx.2.2.2⟩
  have htarget_nonempty : (rectangle 0 (L + 1) 2 3).Nonempty := by
    refine ⟨planePoint 0 2, ?_⟩
    norm_num [rectangle, planePoint]
    linarith
  have hlower : 2 - x 1 ≤ Metric.infDist x (rectangle 0 (L + 1) 2 3) := by
    apply (Metric.le_infDist htarget_nonempty).mpr
    intro y hy
    change 0 ≤ y 0 ∧ y 0 ≤ L + 1 ∧ 2 ≤ y 1 ∧ y 1 ≤ 3 at hy
    have hxy : x 1 ≤ y 1 := by linarith [hcoords.2.2.2]
    calc
      2 - x 1 ≤ y 1 - x 1 := sub_le_sub_right hy.2.2.1 _
      _ ≤ dist x y := SAP.P004b.WH.W2.P.T16_L1.vertical_gap_le_dist x y hxy
  have hproj : planePoint (x 0) 2 ∈ rectangle 0 (L + 1) 2 3 := by
    change 0 ≤ x 0 ∧ x 0 ≤ L + 1 ∧ 2 ≤ 2 ∧ 2 ≤ 3
    exact ⟨hcoords.1, hcoords.2.1, le_rfl, by norm_num⟩
  have hupper : Metric.infDist x (rectangle 0 (L + 1) 2 3) ≤ 2 - x 1 := by
    calc
      Metric.infDist x (rectangle 0 (L + 1) 2 3) ≤ dist x (planePoint (x 0) 2) :=
        Metric.infDist_le_dist_of_mem hproj
      _ = |x 1 - 2| :=
        SAP.P004b.WH.W2.P.T16_L1.vertical_projection_dist x
      _ = 2 - x 1 := by
        rw [abs_of_nonpos (by linarith [hcoords.2.2.2])]
        ring
  have heq : Metric.infDist x (rectangle 0 (L + 1) 2 3) = 2 - x 1 :=
    le_antisymm hupper hlower
  exact ⟨heq, by rw [heq]; linarith [hcoords.2.2.2],
    by rw [heq]; linarith [hcoords.2.2.1]⟩
