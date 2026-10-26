import AronowAudit.P011.Wave1.PropositionOneBlueprint

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PropositionOne

open AronowAudit.P011 MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

private lemma path_linear_sign_bound (u : Fin 2 → Bool) :
    |∑ r, ∑ s, oracleMatrix pathGraph r s *
      pathBlock 2 (sign (u 0)) (sign (u 1)) s| ≤ 61 / 5 := by
  cases h0 : u 0 <;> cases h1 : u 1 <;>
    norm_num [h0, h1, pathBlock, sign, oracleMatrix, adjacency, pathGraph,
      Matrix.add_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem n9_proof : N9 := by
  classical
  intro h2 k
  have hK : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hsource (u : Fin (k + 1) → Fin 2 → Bool) :
      |pathLbar (k + 1) (pathSource (k + 1) u)| ≤ 61 / 5 := by
    unfold pathLbar
    rw [((h2 (k + 1)).1 (pathSource (k + 1) u)).2.2]
    simp_rw [(h2 (k + 1)).2 u]
    rw [abs_div, abs_of_pos hK]
    apply (div_le_iff₀ hK).mpr
    calc
      |∑ b, ∑ r, ∑ s, oracleMatrix pathGraph r s *
          pathBlock 2 (sign (u b 0)) (sign (u b 1)) s| ≤
          ∑ b, |∑ r, ∑ s, oracleMatrix pathGraph r s *
            pathBlock 2 (sign (u b 0)) (sign (u b 1)) s| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _b : Fin (k + 1), (61 / 5 : ℝ) :=
        Finset.sum_le_sum (fun b _ => path_linear_sign_bound (u b))
      _ = (61 / 5) * ((k + 1 : ℕ) : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hf : Measurable (pathSource (k + 1)) := measurable_of_finite _
  have hmeas : MeasurableSet {y : Fin (3 * (k + 1)) → ℝ |
      |pathLbar (k + 1) y| ≤ 61 / 5} := by
    unfold pathLbar
    exact measurableSet_le (by fun_prop) measurable_const
  change ∀ᵐ y ∂uniformLaw (pathSource (k + 1)), |pathLbar (k + 1) y| ≤ 61 / 5
  rw [uniformLaw, ← PMF.toMeasure_map (pathSource (k + 1))
    (PMF.uniformOfFintype (Fin (k + 1) → Fin 2 → Bool)) hf]
  apply (ae_map_iff hf.aemeasurable hmeas).mpr
  exact ae_of_all _ hsource

end

end AronowAudit.P011.Wave1.PropositionOne
