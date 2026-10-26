import AronowAudit.P001.Wave1.QuadraticUniqueBlpBlueprint

namespace AronowAudit.P001.Wave1.QuadraticUniqueBlp

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableQuadraticUniqueBlpN1 (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem n1_proof : N1 := by
  intro Ω _ μ _ X W hX hW hx hw
  -- The direct moment argument in
  -- `uniform_quadratic_cef_and_blp` needs no independence hypothesis.
  have hU2 : MemLp id 2 (uniformLaw 0 1) := by
    rw [uniformLaw_zero_one_eq_restrict]
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    exact (continuous_pow 2).continuousOn.integrableOn_Icc
  have hUU2 : MemLp (fun x : ℝ => x ^ 2) 2 (uniformLaw 0 1) := by
    rw [uniformLaw_zero_one_eq_restrict]
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    have h4 : Integrable (fun x : ℝ => x ^ 4)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      (continuous_pow 4).continuousOn.integrableOn_Icc
    exact h4.congr (ae_of_all _ (fun x => by ring))
  have hX2m : MemLp id 2 (μ.map X) := by rw [hx]; exact hU2
  have hXX2m : MemLp (fun x : ℝ => x ^ 2) 2 (μ.map X) := by rw [hx]; exact hUU2
  have hW2m : MemLp id 2 (μ.map W) := by
    rw [hw]
    exact memLp_id_gaussianReal' 2 (by norm_num)
  exact ⟨hX2m.comp_of_map hX.aemeasurable,
    hXX2m.comp_of_map hX.aemeasurable, hW2m.comp_of_map hW.aemeasurable⟩

end
end AronowAudit.P001.Wave1.QuadraticUniqueBlp
