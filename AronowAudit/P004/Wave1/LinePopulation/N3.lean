import AronowAudit.P004.Wave1.LinePopulation.N2

namespace AronowAudit.P004.Wave1.LinePopulation

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem line_zero_ball {N : ℕ} (R : CircleTable N) (i : Fin N) :
    ball (nodeSeparation (linePopulation R)) i 0 = {i} := by
  ext j
  simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hj
    rw [n1_proof R i j] at hj
    have habs : |(i : ℝ) - (j : ℝ)| = 0 := by
      have := abs_nonneg ((i : ℝ) - (j : ℝ))
      linarith
    have hij : (i : ℝ) = (j : ℝ) := sub_eq_zero.mp (abs_eq_zero.mp habs)
    apply Fin.val_injective
    exact_mod_cast hij.symm
  · rintro rfl
    simp [n1_proof R]

theorem n3_proof : N3 := by
  intro N R
  funext i z
  rw [n2_proof R 0 le_rfl i z, line_zero_ball]
  simp

end
end AronowAudit.P004.Wave1.LinePopulation
