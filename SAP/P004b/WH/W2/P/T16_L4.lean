import SAP.P004b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2.P.T16_L4

open scoped Classical Topology

lemma dist_le_of_coord_sq (x y z : EuclideanSpace ℝ (Fin 2))
    (h0 : (x 0 - y 0) ^ 2 ≤ (x 0 - z 0) ^ 2)
    (h1 : (x 1 - y 1) ^ 2 ≤ (x 1 - z 1) ^ 2) :
    dist x y ≤ dist x z := by
  have hs : dist x y ^ 2 ≤ dist x z ^ 2 := by
    rw [AronowAudit.P004.Wave1.spacing_dist_sq,
      AronowAudit.P004.Wave1.spacing_dist_sq]
    exact add_le_add h0 h1
  exact (sq_le_sq₀ (dist_nonneg) (dist_nonneg)).1 hs

lemma infDist_eq_closest {S : Set (EuclideanSpace ℝ (Fin 2))}
    {x q : EuclideanSpace ℝ (Fin 2)} (hq : q ∈ S)
    (hmin : ∀ y ∈ S, dist x q ≤ dist x y) :
    Metric.infDist x S = dist x q := by
  apply le_antisymm
  · exact Metric.infDist_le_dist_of_mem hq
  · exact (Metric.le_infDist ⟨q, hq⟩).2 hmin

lemma dist_eq_one_of_sq {x y : EuclideanSpace ℝ (Fin 2)}
    (h : dist x y ^ 2 = 1) : dist x y = 1 := by
  have hl : 1 ≤ dist x y :=
    (sq_le_sq₀ (by norm_num) dist_nonneg).1 (by rw [h]; norm_num)
  have hu : dist x y ≤ 1 :=
    (sq_le_sq₀ dist_nonneg (by norm_num)).1 (by rw [h]; norm_num)
  exact le_antisymm hu hl

lemma vertical_left :
    Metric.infDist (SAP.P004b.planePoint (1/2) 2)
      (SAP.P004b.rectangle 0 1 0 1) = 1 := by
  let x := SAP.P004b.planePoint (1/2) 2
  let q := SAP.P004b.planePoint (1/2) 1
  have hq : q ∈ SAP.P004b.rectangle 0 1 0 1 := by
    norm_num [q, SAP.P004b.planePoint, SAP.P004b.rectangle]
  have hdistSq : dist x q ^ 2 = 1 := by
    rw [AronowAudit.P004.Wave1.spacing_dist_sq]
    norm_num [x, q, SAP.P004b.planePoint]
  have hdist := dist_eq_one_of_sq hdistSq
  rw [infDist_eq_closest hq]
  · exact hdist
  · intro y hy
    rcases hy with ⟨hy0, hy1, hy2, hy3⟩
    apply dist_le_of_coord_sq
    · have heq : x 0 = q 0 := by norm_num [x, q, SAP.P004b.planePoint]
      rw [heq]
      simpa using sq_nonneg (q 0 - y 0)
    · have hx : x 1 - q 1 = 1 := by norm_num [x, q, SAP.P004b.planePoint]
      have hyx : 0 ≤ x 1 - y 1 := by norm_num [x, SAP.P004b.planePoint]; linarith
      have hle : x 1 - q 1 ≤ x 1 - y 1 := by
        rw [hx]
        norm_num [x, SAP.P004b.planePoint]
        linarith
      exact (sq_le_sq₀ (by rw [hx]; norm_num) hyx).2 hle

lemma vertical_right :
    Metric.infDist (SAP.P004b.planePoint (21/2) 2)
      (SAP.P004b.rectangle 10 11 0 1) = 1 := by
  let x := SAP.P004b.planePoint (21/2) 2
  let q := SAP.P004b.planePoint (21/2) 1
  have hq : q ∈ SAP.P004b.rectangle 10 11 0 1 := by
    norm_num [q, SAP.P004b.planePoint, SAP.P004b.rectangle]
  have hdistSq : dist x q ^ 2 = 1 := by
    rw [AronowAudit.P004.Wave1.spacing_dist_sq]
    norm_num [x, q, SAP.P004b.planePoint]
  have hdist := dist_eq_one_of_sq hdistSq
  rw [infDist_eq_closest hq]
  · exact hdist
  · intro y hy
    rcases hy with ⟨hy0, hy1, hy2, hy3⟩
    apply dist_le_of_coord_sq
    · have heq : x 0 = q 0 := by norm_num [x, q, SAP.P004b.planePoint]
      rw [heq]
      simpa using sq_nonneg (q 0 - y 0)
    · have hx : x 1 - q 1 = 1 := by norm_num [x, q, SAP.P004b.planePoint]
      have hyx : 0 ≤ x 1 - y 1 := by norm_num [x, SAP.P004b.planePoint]; linarith
      have hle : x 1 - q 1 ≤ x 1 - y 1 := by
        rw [hx]
        norm_num [x, SAP.P004b.planePoint]
        linarith
      exact (sq_le_sq₀ (by rw [hx]; norm_num) hyx).2 hle

lemma vertical_top (a : Bool) :
    Metric.infDist (SAP.P004b.positiveAtom a)
      (SAP.P004b.rectangle 0 11 3 4) = 1 := by
  cases a
  · change Metric.infDist (SAP.P004b.planePoint (1/2) 2)
      (SAP.P004b.rectangle 0 11 3 4) = 1
    let x := SAP.P004b.planePoint (1/2) 2
    let q := SAP.P004b.planePoint (1/2) 3
    have hq : q ∈ SAP.P004b.rectangle 0 11 3 4 := by
      norm_num [q, SAP.P004b.planePoint, SAP.P004b.rectangle]
    have hdistSq : dist x q ^ 2 = 1 := by
      rw [AronowAudit.P004.Wave1.spacing_dist_sq]
      norm_num [x, q, SAP.P004b.planePoint]
    have hdist := dist_eq_one_of_sq hdistSq
    rw [infDist_eq_closest hq]
    · exact hdist
    · intro y hy
      rcases hy with ⟨hy0, hy1, hy2, hy3⟩
      apply dist_le_of_coord_sq
      · have heq : x 0 = q 0 := by norm_num [x, q, SAP.P004b.planePoint]
        rw [heq]
        simpa using sq_nonneg (q 0 - y 0)
      · have hx : q 1 - x 1 = 1 := by norm_num [x, q, SAP.P004b.planePoint]
        have hyx : 0 ≤ y 1 - x 1 := by norm_num [x, SAP.P004b.planePoint]; linarith
        have hle : q 1 - x 1 ≤ y 1 - x 1 := by
          rw [hx]
          norm_num [x, SAP.P004b.planePoint]
          linarith
        have hsq : (x 1 - q 1) ^ 2 ≤ (x 1 - y 1) ^ 2 := by
          have hrev : (q 1 - x 1) ^ 2 ≤ (y 1 - x 1) ^ 2 :=
            (sq_le_sq₀ (by rw [hx]; norm_num) hyx).2 hle
          nlinarith
        exact hsq
  · change Metric.infDist (SAP.P004b.planePoint (21/2) 2)
      (SAP.P004b.rectangle 0 11 3 4) = 1
    let x := SAP.P004b.planePoint (21/2) 2
    let q := SAP.P004b.planePoint (21/2) 3
    have hq : q ∈ SAP.P004b.rectangle 0 11 3 4 := by
      norm_num [q, SAP.P004b.planePoint, SAP.P004b.rectangle]
    have hdistSq : dist x q ^ 2 = 1 := by
      rw [AronowAudit.P004.Wave1.spacing_dist_sq]
      norm_num [x, q, SAP.P004b.planePoint]
    have hdist := dist_eq_one_of_sq hdistSq
    rw [infDist_eq_closest hq]
    · exact hdist
    · intro y hy
      rcases hy with ⟨hy0, hy1, hy2, hy3⟩
      apply dist_le_of_coord_sq
      · have heq : x 0 = q 0 := by norm_num [x, q, SAP.P004b.planePoint]
        rw [heq]
        simpa using sq_nonneg (q 0 - y 0)
      · have hx : q 1 - x 1 = 1 := by norm_num [x, q, SAP.P004b.planePoint]
        have hyx : 0 ≤ y 1 - x 1 := by norm_num [x, SAP.P004b.planePoint]; linarith
        have hle : q 1 - x 1 ≤ y 1 - x 1 := by
          rw [hx]
          norm_num [x, SAP.P004b.planePoint]
          linarith
        have hrev : (q 1 - x 1) ^ 2 ≤ (y 1 - x 1) ^ 2 :=
          (sq_le_sq₀ (by rw [hx]; norm_num) hyx).2 hle
        nlinarith

lemma cross_left :
    Metric.infDist (SAP.P004b.planePoint (21/2) 2)
      (SAP.P004b.rectangle 0 1 0 1) =
        dist (SAP.P004b.planePoint (21/2) 2) (SAP.P004b.planePoint 1 1) := by
  let x := SAP.P004b.planePoint (21/2) 2
  let q := SAP.P004b.planePoint 1 1
  have hq : q ∈ SAP.P004b.rectangle 0 1 0 1 := by
    norm_num [q, SAP.P004b.planePoint, SAP.P004b.rectangle]
  apply infDist_eq_closest hq
  intro y hy
  rcases hy with ⟨hy0, hy1, hy2, hy3⟩
  apply dist_le_of_coord_sq
  · have hx : x 0 - q 0 = 19/2 := by norm_num [x, q, SAP.P004b.planePoint]
    have hyx : 0 ≤ x 0 - y 0 := by norm_num [x, SAP.P004b.planePoint]; linarith
    have hle : x 0 - q 0 ≤ x 0 - y 0 := by rw [hx]; norm_num [x, SAP.P004b.planePoint]; linarith
    exact (sq_le_sq₀ (by rw [hx]; norm_num) hyx).2 hle
  · have hx : x 1 - q 1 = 1 := by norm_num [x, q, SAP.P004b.planePoint]
    have hyx : 0 ≤ x 1 - y 1 := by norm_num [x, SAP.P004b.planePoint]; linarith
    have hle : x 1 - q 1 ≤ x 1 - y 1 := by rw [hx]; norm_num [x, SAP.P004b.planePoint]; linarith
    exact (sq_le_sq₀ (by rw [hx]; norm_num) hyx).2 hle

lemma cross_right :
    Metric.infDist (SAP.P004b.planePoint (1/2) 2)
      (SAP.P004b.rectangle 10 11 0 1) =
        dist (SAP.P004b.planePoint (1/2) 2) (SAP.P004b.planePoint 10 1) := by
  let x := SAP.P004b.planePoint (1/2) 2
  let q := SAP.P004b.planePoint 10 1
  have hq : q ∈ SAP.P004b.rectangle 10 11 0 1 := by
    norm_num [q, SAP.P004b.planePoint, SAP.P004b.rectangle]
  apply infDist_eq_closest hq
  intro y hy
  rcases hy with ⟨hy0, hy1, hy2, hy3⟩
  apply dist_le_of_coord_sq
  · have hx : q 0 - x 0 = 19/2 := by norm_num [x, q, SAP.P004b.planePoint]
    have hyx : 0 ≤ y 0 - x 0 := by norm_num [x, SAP.P004b.planePoint]; linarith
    have hle : q 0 - x 0 ≤ y 0 - x 0 := by rw [hx]; norm_num [x, SAP.P004b.planePoint]; linarith
    have hrev : (q 0 - x 0) ^ 2 ≤ (y 0 - x 0) ^ 2 :=
      (sq_le_sq₀ (by rw [hx]; norm_num) hyx).2 hle
    nlinarith
  · have hx : x 1 - q 1 = 1 := by norm_num [x, q, SAP.P004b.planePoint]
    have hyx : 0 ≤ x 1 - y 1 := by norm_num [x, SAP.P004b.planePoint]; linarith
    have hle : x 1 - q 1 ≤ x 1 - y 1 := by rw [hx]; norm_num [x, SAP.P004b.planePoint]; linarith
    exact (sq_le_sq₀ (by rw [hx]; norm_num) hyx).2 hle

end SAP.P004b.WH.W2.P.T16_L4

open SAP.P004b.WH.W2.P.T16_L4

theorem SAP.P004b.WH.W2.T16_L4_proof : SAP.P004b.WH.W2.T16_L4 := by
  constructor
  · change Metric.infDist (SAP.P004b.planePoint (1/2) 2)
      (SAP.P004b.rectangle 0 1 0 1) = 1
    exact vertical_left
  constructor
  · change Metric.infDist (SAP.P004b.planePoint (21/2) 2)
      (SAP.P004b.rectangle 10 11 0 1) = 1
    exact vertical_right
  constructor
  · intro a
    change Metric.infDist (SAP.P004b.positiveAtom a)
      (SAP.P004b.rectangle 0 11 3 4) = 1
    exact vertical_top a
  constructor
  · change (Metric.infDist (SAP.P004b.planePoint (21/2) 2)
      (SAP.P004b.rectangle 0 1 0 1)) ^ 2 = 365/4
    rw [cross_left]
    rw [AronowAudit.P004.Wave1.spacing_dist_sq]
    norm_num [SAP.P004b.planePoint]
  · change (Metric.infDist (SAP.P004b.planePoint (1/2) 2)
      (SAP.P004b.rectangle 10 11 0 1)) ^ 2 = 365/4
    rw [cross_right]
    rw [AronowAudit.P004.Wave1.spacing_dist_sq]
    norm_num [SAP.P004b.planePoint]

