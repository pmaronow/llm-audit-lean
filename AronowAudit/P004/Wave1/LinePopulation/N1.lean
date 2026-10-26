import AronowAudit.P004.Wave1.LinePopulationBlueprint

namespace AronowAudit.P004.Wave1.LinePopulation

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Distances on the horizontal axis, in the actual Euclidean metric. -/
theorem line_point_dist (a b : ℝ) :
    dist (planePoint a 0) (planePoint b 0) = |a - b| := by
  rw [EuclideanSpace.dist_eq]
  simp [planePoint, Fin.sum_univ_two, Real.dist_eq, Real.sqrt_sq_eq_abs]

/-- The infimum defining separation is the distance of the two singleton nodes. -/
theorem line_separation_eq_dist {N : ℕ} (R : CircleTable N) (i j : Fin N) :
    nodeSeparation (linePopulation R) i j =
      dist (planePoint (10 * (i : ℝ)) 0) (planePoint (10 * (j : ℝ)) 0) := by
  simp [nodeSeparation, linePopulation]

/-- The support points are distinct, including for arbitrary population size. -/
theorem line_point_injective {N : ℕ} :
    Function.Injective (fun i : Fin N => planePoint (10 * (i : ℝ)) 0) := by
  intro i j hij
  have hcoord := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hij
  have hx : 10 * (i : ℝ) = 10 * (j : ℝ) := by
    simpa [planePoint] using hcoord
  have hv : (i : ℝ) = (j : ℝ) := by linarith
  apply Fin.val_injective
  exact_mod_cast hv

theorem n1_proof : N1 := by
  intro N R i j
  rw [line_separation_eq_dist, line_point_dist, ← mul_sub, abs_mul]
  norm_num

end
end AronowAudit.P004.Wave1.LinePopulation
