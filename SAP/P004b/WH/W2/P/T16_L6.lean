import SAP.P004b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2.P.T16_L6

open scoped Classical

noncomputable section

open SAP.P004b

lemma rectangle_closed (a b c d : ℝ) : IsClosed (rectangle a b c d) := by
  let E := EuclideanSpace ℝ (Fin 2)
  have h0 : Continuous (fun x : E => x 0) :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0
  have h1 : Continuous (fun x : E => x 1) :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1
  have h00 : IsClosed {x : E | a ≤ x 0} :=
    isClosed_le (continuous_const : Continuous fun _ : E => a) h0
  have h01 : IsClosed {x : E | x 0 ≤ b} :=
    isClosed_le h0 (continuous_const : Continuous fun _ : E => b)
  have h10 : IsClosed {x : E | c ≤ x 1} :=
    isClosed_le (continuous_const : Continuous fun _ : E => c) h1
  have h11 : IsClosed {x : E | x 1 ≤ d} :=
    isClosed_le h1 (continuous_const : Continuous fun _ : E => d)
  change IsClosed ({x : E | a ≤ x 0} ∩
    ({x : E | x 0 ≤ b} ∩ ({x : E | c ≤ x 1} ∩ {x : E | x 1 ≤ d})))
  exact h00.inter (h01.inter (h10.inter h11))

lemma compact_left_rectangle : IsCompact (rectangle 0 1 0 1) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · exact rectangle_closed 0 1 0 1
  · apply (isBounded_iff_forall_norm_le (s := rectangle 0 1 0 1)).2
    refine ⟨2, ?_⟩
    intro x hx
    simp only [rectangle, Set.mem_setOf_eq] at hx
    rcases hx with ⟨hx0, hx01, hx1, hx11⟩
    have hnorm : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_two]
    have hsq : ‖x‖ ^ 2 ≤ 4 := by
      rw [hnorm]
      nlinarith
    have hn : 0 ≤ ‖x‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖x‖ - 2)]

lemma compact_right_rectangle : IsCompact (rectangle 10 11 0 1) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · exact rectangle_closed 10 11 0 1
  · apply (isBounded_iff_forall_norm_le (s := rectangle 10 11 0 1)).2
    refine ⟨12, ?_⟩
    intro x hx
    simp only [rectangle, Set.mem_setOf_eq] at hx
    rcases hx with ⟨hx0, hx01, hx1, hx11⟩
    have hnorm : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_two]
    have hsq : ‖x‖ ^ 2 ≤ 144 := by
      rw [hnorm]
      nlinarith
    have hn : 0 ≤ ‖x‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖x‖ - 12)]

lemma coord_sub_le_dist (x y : EuclideanSpace ℝ (Fin 2)) :
    x 0 - y 0 ≤ dist x y := by
  have hsq : |x 0 - y 0| ^ 2 ≤ dist x y ^ 2 := by
    rw [sq_abs, AronowAudit.P004.Wave1.spacing_dist_sq]
    nlinarith [sq_nonneg (x 1 - y 1)]
  have habs : 0 ≤ |x 0 - y 0| := abs_nonneg _
  have hdist : 0 ≤ dist x y := dist_nonneg
  calc
    x 0 - y 0 ≤ |x 0 - y 0| := le_abs_self _
    _ ≤ dist x y := (sq_le_sq₀ habs hdist).mp hsq

lemma first_contour_coordinate (x : EuclideanSpace ℝ (Fin 2))
    (hx : x ∈ region positiveRectangleWitness 0 1) : x 0 ≤ 2 := by
  have hxinf : Metric.infDist x (rectangle 0 1 0 1) = 1 := by
    simpa [region, nodeDistance, positiveRectangleWitness] using hx
  obtain ⟨a, ha, hda⟩ := compact_left_rectangle.exists_infDist_eq_dist
    (positiveRectangleWitness.node_nonempty 0) x
  have hdist : dist x a = 1 := by
    rw [← hda, hxinf]
  have ha' : a ∈ rectangle 0 1 0 1 := by simpa [positiveRectangleWitness] using ha
  simp only [rectangle, Set.mem_setOf_eq] at ha'
  have hcoord := coord_sub_le_dist x a
  linarith [hdist]

lemma second_contour_coordinate (y : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ region positiveRectangleWitness 1 1) : 9 ≤ y 0 := by
  have hyinf : Metric.infDist y (rectangle 10 11 0 1) = 1 := by
    simpa [region, nodeDistance, positiveRectangleWitness] using hy
  obtain ⟨b, hb, hdb⟩ := compact_right_rectangle.exists_infDist_eq_dist
    (positiveRectangleWitness.node_nonempty 1) y
  have hdist : dist y b = 1 := by
    rw [← hdb, hyinf]
  have hb' : b ∈ rectangle 10 11 0 1 := by simpa [positiveRectangleWitness] using hb
  simp only [rectangle, Set.mem_setOf_eq] at hb'
  have hcoord := coord_sub_le_dist b y
  have hdist' : dist b y = 1 := by simpa [dist_comm] using hdist
  linarith [hdist']


end
end SAP.P004b.WH.W2.P.T16_L6

open SAP.P004b
open SAP.P004b.WH.W2.P.T16_L6

theorem SAP.P004b.WH.W2.T16_L6_proof : SAP.P004b.WH.W2.T16_L6 := by
  let x : EuclideanSpace ℝ (Fin 2) := planePoint 2 (1 / 2)
  let y : EuclideanSpace ℝ (Fin 2) := planePoint 9 (1 / 2)
  let a : EuclideanSpace ℝ (Fin 2) := planePoint 1 (1 / 2)
  let b : EuclideanSpace ℝ (Fin 2) := planePoint 10 (1 / 2)
  have ha : a ∈ rectangle 0 1 0 1 := by
    norm_num [a, planePoint, rectangle]
  have hb : b ∈ rectangle 10 11 0 1 := by
    norm_num [b, planePoint, rectangle]
  have hxa : dist x a = 1 := by
    have hs : dist x a ^ 2 = 1 := by
      rw [AronowAudit.P004.Wave1.spacing_dist_sq]
      norm_num [x, a, planePoint]
    have hnon : 0 ≤ dist x a := dist_nonneg
    nlinarith [hs, hnon, sq_nonneg (dist x a - 1)]
  have hyb : dist y b = 1 := by
    have hs : dist y b ^ 2 = 1 := by
      rw [AronowAudit.P004.Wave1.spacing_dist_sq]
      norm_num [y, b, planePoint]
    have hnon : 0 ≤ dist y b := dist_nonneg
    nlinarith [hs, hnon, sq_nonneg (dist y b - 1)]
  have hxinf : Metric.infDist x (rectangle 0 1 0 1) = 1 := by
    apply le_antisymm
    · exact (Metric.infDist_le_dist_of_mem ha).trans_eq hxa
    · apply (Metric.le_infDist ⟨a, ha⟩).2
      intro z hz
      simp only [rectangle, Set.mem_setOf_eq] at hz
      have hcoord := coord_sub_le_dist x z
      calc
        1 ≤ x 0 - z 0 := by norm_num [x, planePoint]; linarith
        _ ≤ dist x z := hcoord
  have hyinf : Metric.infDist y (rectangle 10 11 0 1) = 1 := by
    apply le_antisymm
    · exact (Metric.infDist_le_dist_of_mem hb).trans_eq hyb
    · apply (Metric.le_infDist ⟨b, hb⟩).2
      intro z hz
      simp only [rectangle, Set.mem_setOf_eq] at hz
      have hcoord := coord_sub_le_dist z y
      calc
        1 ≤ z 0 - y 0 := by norm_num [y, planePoint]; linarith
        _ ≤ dist y z := by simpa [dist_comm] using hcoord
  have hx : x ∈ region positiveRectangleWitness 0 1 := by
    simpa [region, nodeDistance, positiveRectangleWitness] using hxinf
  have hy : y ∈ region positiveRectangleWitness 1 1 := by
    simpa [region, nodeDistance, positiveRectangleWitness] using hyinf
  have hxy : dist x y = 7 := by
    have hs : dist x y ^ 2 = 49 := by
      rw [AronowAudit.P004.Wave1.spacing_dist_sq]
      norm_num [x, y, planePoint]
    have hnon : 0 ≤ dist x y := dist_nonneg
    nlinarith [hs, hnon, sq_nonneg (dist x y - 7)]
  constructor
  · change planeSeparation (region positiveRectangleWitness 0 1)
      (region positiveRectangleWitness 1 1) = 7
    unfold planeSeparation
    apply le_antisymm
    · apply csInf_le
      · refine ⟨0, ?_⟩
        rintro r ⟨u, hu, v, hv, rfl⟩
        exact dist_nonneg
      · exact ⟨x, hx, y, hy, hxy⟩
    · apply le_csInf
      · exact ⟨7, x, hx, y, hy, hxy⟩
      · rintro r ⟨u, hu, v, hv, rfl⟩
        have hu' := first_contour_coordinate u hu
        have hv' := second_contour_coordinate v hv
        have hcoord := coord_sub_le_dist v u
        calc
          7 ≤ v 0 - u 0 := by linarith
          _ ≤ dist u v := by simpa [dist_comm] using hcoord
  · exact ⟨x, hx, y, hy, hxy⟩
