import SAP.P001g.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g.WH.W2.P.T121_L1

open scoped BigOperators

private theorem affine_midpoint (z v : Fin 2 → ℝ) (y : Fin 3) :
    circleAffineW2 (fun j => (1 / 2 : ℝ) * z j + (1 / 2 : ℝ) * v j) y =
      (1 / 2 : ℝ) * circleAffineW2 z y + (1 / 2 : ℝ) * circleAffineW2 v y := by
  fin_cases y <;> simp [circleAffineW2] <;> ring

private theorem midpoint_mem_disc (z v : Fin 2 → ℝ)
    (hz : z ∈ circleDiscW2) (hv : v ∈ circleDiscW2) :
    (fun j => (1 / 2 : ℝ) * z j + (1 / 2 : ℝ) * v j) ∈ circleDiscW2 := by
  change z 0 ^ 2 + z 1 ^ 2 ≤ 1 at hz
  change v 0 ^ 2 + v 1 ^ 2 ≤ 1 at hv
  change ((1 / 2 : ℝ) * z 0 + (1 / 2 : ℝ) * v 0) ^ 2 +
    ((1 / 2 : ℝ) * z 1 + (1 / 2 : ℝ) * v 1) ^ 2 ≤ 1
  nlinarith [sq_nonneg (z 0 - v 0), sq_nonneg (z 1 - v 1)]

end SAP.P001g.WH.W2.P.T121_L1

open SAP.P001g.WH.W2.P.T121_L1

theorem SAP.P001g.WH.W2.T121_L1_proof : SAP.P001g.WH.W2.T121_L1 := by
  intro n s z v hz hv hmz hmv i
  by_contra h
  let m : Fin 2 → ℝ := fun j => (1 / 2 : ℝ) * z j + (1 / 2 : ℝ) * v j
  have hm : m ∈ circleDiscW2 := by
    simpa [m] using midpoint_mem_disc z v hz hv
  have hpos (w : Fin 2 → ℝ) (hw : w ∈ circleDiscW2) :
      0 < circleDiscLikeW2 s w := by
    unfold circleDiscLikeW2
    exact Finset.prod_pos fun j _ => affinePosW2 w hw (s j)
  have hlog (w : Fin 2 → ℝ) (hw : w ∈ circleDiscW2) :
      Real.log (circleDiscLikeW2 s w) =
        ∑ j, Real.log (circleAffineW2 w (s j)) := by
    simp only [circleDiscLikeW2]
    rw [Real.log_prod (fun j _ => (affinePosW2 w hw (s j)).ne')]
  have hmaxEq : circleDiscLikeW2 s z = circleDiscLikeW2 s v := by
    apply le_antisymm
    · exact hmv hz
    · exact hmz hv
  have hlogEq :
      Real.log (circleDiscLikeW2 s z) = Real.log (circleDiscLikeW2 s v) := by
    rw [hmaxEq]
  have hlogMax : Real.log (circleDiscLikeW2 s m) ≤
      Real.log (circleDiscLikeW2 s z) := by
    apply Real.log_le_log (hpos m hm)
    exact hmz hm
  have hdiff : circleAffineW2 z (s i) ≠ circleAffineW2 v (s i) := by
    intro heq
    exact h heq
  have hstrict :
      (1 / 2 : ℝ) * Real.log (circleAffineW2 z (s i)) +
          (1 / 2 : ℝ) * Real.log (circleAffineW2 v (s i)) <
        Real.log (circleAffineW2 m (s i)) := by
    have h := strictConcaveOn_log_Ioi.2
      (affinePosW2 z hz (s i)) (affinePosW2 v hv (s i)) hdiff
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    rw [show circleAffineW2 m (s i) =
        (1 / 2 : ℝ) * circleAffineW2 z (s i) +
          (1 / 2 : ℝ) * circleAffineW2 v (s i) from by
          dsimp [m]
          exact affine_midpoint z v (s i)]
    simpa [smul_eq_mul] using h
  have hconc (j : Fin n) :
      (1 / 2 : ℝ) * Real.log (circleAffineW2 z (s j)) +
          (1 / 2 : ℝ) * Real.log (circleAffineW2 v (s j)) ≤
        Real.log (circleAffineW2 m (s j)) := by
    have h := strictConcaveOn_log_Ioi.concaveOn.2
      (affinePosW2 z hz (s j)) (affinePosW2 v hv (s j))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    rw [show circleAffineW2 m (s j) =
        (1 / 2 : ℝ) * circleAffineW2 z (s j) +
          (1 / 2 : ℝ) * circleAffineW2 v (s j) from by
          dsimp [m]
          exact affine_midpoint z v (s j)]
    simpa [smul_eq_mul] using h
  have hsum :
      (∑ j : Fin n,
        ((1 / 2 : ℝ) * Real.log (circleAffineW2 z (s j)) +
          (1 / 2 : ℝ) * Real.log (circleAffineW2 v (s j)))) <
        ∑ j : Fin n, Real.log (circleAffineW2 m (s j)) := by
    exact Finset.sum_lt_sum (fun j _ => hconc j) ⟨i, Finset.mem_univ _, hstrict⟩
  have hsumMid :
      (∑ j : Fin n,
        ((1 / 2 : ℝ) * Real.log (circleAffineW2 z (s j)) +
          (1 / 2 : ℝ) * Real.log (circleAffineW2 v (s j)))) =
        (1 / 2 : ℝ) * Real.log (circleDiscLikeW2 s z) +
          (1 / 2 : ℝ) * Real.log (circleDiscLikeW2 s v) := by
    rw [hlog z hz, hlog v hv]
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hlog m hm] at hlogMax
  rw [hsumMid] at hsum
  rw [hlogEq] at hsum
  linarith
