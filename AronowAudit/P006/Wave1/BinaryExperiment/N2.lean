import AronowAudit.P006.Wave1.BinaryExperimentBlueprint

set_option autoImplicit false
namespace AronowAudit.P006.Wave1.BinaryExperiment
open AronowAudit.P006 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section

theorem n2_proof : N2 := by
  classical
  intro h1 n π hπ f
  have hnon (i : Fin n) (ω : Fin n → Bool × Bool) :
      0 ≤ (1 / 2 : ℝ) * coinMass (π (ω i).1) (ω i).2 :=
    mul_nonneg (by norm_num) ((coin_is_probability _ (hπ.2 (ω i).1)).1 _)
  have hatom (ω : Fin n → Bool × Bool) :
      (Measure.pi fun _ : Fin n => unitLaw π) {ω} =
        ∏ i : Fin n, ENNReal.ofReal ((1 / 2) * coinMass (π (ω i).1) (ω i).2) := by
    rw [← Set.univ_pi_singleton, Measure.pi_pi]
    exact Finset.prod_congr rfl (fun i _ => (h1 π hπ).2.1 (ω i))
  rw [integral_fintype (Integrable.of_finite : Integrable f _)]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [measureReal_def, hatom, ENNReal.toReal_prod, smul_eq_mul]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => ENNReal.toReal_ofReal (hnon i ω))

end
end AronowAudit.P006.Wave1.BinaryExperiment
