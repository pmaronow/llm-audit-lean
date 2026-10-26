import AronowAudit.P011.Wave1.PropositionOneBlueprint

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PropositionOne

open AronowAudit.P011 MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- Expand centering at the single, global sample mean. -/
private lemma centered_quadratic_expansion {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, M i j = M j i)
    (y : Fin n → ℝ) :
    quadratic M (centered y) = quadratic M y -
      2 * average y * (∑ i, ∑ j, M i j * y j) +
      average y ^ 2 * (∑ i, ∑ j, M i j) := by
  classical
  have hlinear : (∑ i, ∑ j, M i j * y i) = (∑ i, ∑ j, M i j * y j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hM j i]
  have hentry (i j : Fin n) :
      M i j * (y i - average y) * (y j - average y) =
        M i j * y i * y j - average y * (M i j * y i) -
        average y * (M i j * y j) + average y ^ 2 * M i j := by
    ring
  unfold quadratic centered
  simp_rw [hentry]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hlinear]
  ring

theorem n8_proof : N8 := by
  classical
  intro h2 K hK y
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hsymm (i j : Fin (3 * K)) :
      oracleMatrix (pathGraphK K) i j = oracleMatrix (pathGraphK K) j i := by
    simp only [oracleMatrix, Matrix.add_apply, Matrix.one_apply, adjacency]
    rw [(pathGraphK K).property.1 i j]
    simp only [eq_comm]
  have hpath : quadratic (oracleMatrix pathGraph) (fun _ => 1) = 7 :=
    (path_block_moments 2).2.2.2.2.2.2
  have hblock (b : Fin K) :
      blockVec K (fun _ : Fin (3 * K) => (1 : ℝ)) b = (fun _ => 1) := rfl
  have hones : (∑ i, ∑ j, oracleMatrix (pathGraphK K) i j) = 7 * (K : ℝ) := by
    have h := ((h2 K).1 (fun _ => 1)).2.1
    simp_rw [hblock] at h
    simp only [hpath, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    simpa only [quadratic, mul_one, one_mul, mul_comm] using h
  rw [← variance_form_oracle, varianceForm,
    centered_quadratic_expansion _ hsymm, hones]
  unfold pathQbar pathLbar
  push_cast
  field_simp [hK0]
  <;> ring

end

end AronowAudit.P011.Wave1.PropositionOne
