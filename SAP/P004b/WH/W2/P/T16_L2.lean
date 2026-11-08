import SAP.P004b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2.P.T16_L2

open scoped Classical

theorem rectangle_separation (L : ℝ) (hL : 2 ≤ L) :
    SAP.P004b.planeSeparation (SAP.P004b.rectangle 0 1 0 1)
      (SAP.P004b.rectangle L (L + 1) 0 1) = L - 1 := by
  let S : Set ℝ := {r | ∃ x ∈ SAP.P004b.rectangle 0 1 0 1,
    ∃ y ∈ SAP.P004b.rectangle L (L + 1) 0 1, dist x y = r}
  have hmem : L - 1 ∈ S := by
    refine ⟨SAP.P004b.planePoint 1 0, ?_, SAP.P004b.planePoint L 0, ?_, ?_⟩
    · norm_num [S, SAP.P004b.rectangle, SAP.P004b.planePoint]
    · norm_num [S, SAP.P004b.rectangle, SAP.P004b.planePoint]
    · simp [EuclideanSpace.dist_eq, SAP.P004b.planePoint, Fin.sum_univ_succ,
        Real.dist_eq, Real.sqrt_sq_eq_abs,
        abs_of_nonpos (by linarith : 1 - L ≤ 0)]
  have hlow : ∀ r ∈ S, L - 1 ≤ r := by
    rintro r ⟨x, hx, y, hy, rfl⟩
    change x ∈ SAP.P004b.rectangle 0 1 0 1 at hx
    change y ∈ SAP.P004b.rectangle L (L + 1) 0 1 at hy
    have hcoord : |x 0 - y 0| ≤ dist x y := by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le x y 0
    have hneg : -(x 0 - y 0) ≤ |x 0 - y 0| := neg_le_abs _
    linarith [hx.2.1, hy.1]
  change sInf S = L - 1
  exact le_antisymm (csInf_le ⟨L - 1, hlow⟩ hmem)
    (le_csInf ⟨L - 1, hmem⟩ hlow)

end SAP.P004b.WH.W2.P.T16_L2

theorem SAP.P004b.WH.W2.T16_L2_proof : SAP.P004b.WH.W2.T16_L2 := by
  intro L hL
  exact SAP.P004b.WH.W2.P.T16_L2.rectangle_separation L hL
