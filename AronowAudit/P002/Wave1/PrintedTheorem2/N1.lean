import AronowAudit.P002.Wave1.PrintedTheorem2Blueprint
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace AronowAudit.P002.Wave1.PrintedTheorem2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- The population Gram matrix has no nonzero vector in its kernel. -/
theorem n1_proof : N1 := by
  intro n k P δ e A B r he hXi
  rcases hXi with ⟨hD, _, _, _, _, _, _, hx, _, hQ⟩
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hD.1
  have hbound : ∀ b : Option (Fin k) → ℝ,
      min 1 e * normSq b ≤
        mean (fun i => (dotProduct (augmented P.x i) b) ^ 2) :=
    (corrected_augmented_gram P.x hn e hx hQ).2.2.2
  have hmin : 0 < min (1 : ℝ) e := lt_min (by norm_num) he
  intro hdet
  obtain ⟨b, hb, hGb⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hcoord : ∃ j, b j ≠ 0 := by
    by_contra h
    apply hb
    funext j
    change b j = 0
    by_contra hj
    exact h ⟨j, hj⟩
  have hnorm : 0 < normSq b := by
    unfold normSq
    apply Finset.sum_pos'
    · intro j _
      exact sq_nonneg (b j)
    · obtain ⟨j, hj⟩ := hcoord
      exact ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero hj⟩
  have hzero : mean (fun i => (dotProduct (augmented P.x i) b) ^ 2) = 0 := by
    have hquad := (gram_quadratic P.x Finset.univ b).symm
    simpa [hGb, groupMean, mean] using hquad
  have hle := hbound b
  rw [hzero] at hle
  exact (not_le_of_gt (mul_pos hmin hnorm)) hle

end
end AronowAudit.P002.Wave1.PrintedTheorem2
