import AronowAudit.P047.Wave1.Impossibility.N2

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

theorem n4_proof : N4 := by
  classical
  intro e m he hm heb hmb
  have hg := measurable_gen e m he hm
  have he01 (w : ℝ) : 0 ≤ e w ∧ e w ≤ 1 :=
    ⟨by linarith [(heb w).1], by linarith [(heb w).2]⟩
  have hbin : ∀ a, ∀ᵐ u ∂genMeasure e m, potential a u = 0 ∨ potential a u = 1 := by
    intro a
    change ∀ᵐ u ∂(uniform01.prod (uniform01.prod uniform01)).map (gen e m), _
    apply (ae_map_iff hg.aemeasurable
      (show MeasurableSet {x : UnitData | potential a x = 0 ∨ potential a x = 1} from
        (measurableSet_eq_fun (measurable_potential a) measurable_const).union
          (measurableSet_eq_fun (measurable_potential a) measurable_const))).mpr
    apply ae_of_all
    intro z
    cases a <;> by_cases hy : z.2.2 ≤ m z.1 <;> simp [potential, gen, hy]
  refine ⟨genMeasure_map_covariate e m he hm, hbin, ae_of_all _ (fun u => heb (covariate u)), ?_⟩
  have hF : Integrable (fun u => potential true u - potential false u) (genMeasure e m) := by
    apply Integrable.of_bound
      ((measurable_potential true).sub (measurable_potential false)).aestronglyMeasurable 1
    filter_upwards [hbin true, hbin false] with u ht hf
    rcases ht with ht | ht <;> rcases hf with hf | hf <;> simp only [Pi.sub_apply] <;>
      rw [ht, hf] <;> norm_num
  rw [integral_genMeasure e m he hm he01 hmb _ hF]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  simp only [potential, Bool.false_eq_true, ↓reduceIte, sub_zero, sub_self, mul_one, mul_zero,
    add_zero]
  ring

end

end AronowAudit.P047.Wave1.Impossibility
