import AronowAudit.P029.Wave1.RandomizedProbabilityBlueprint

namespace AronowAudit.P029.Wave1.RandomizedProbability

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

universe u v

noncomputable section

theorem n2_proof : N2.{u, v} := by
  intro Ω A _ _ ν _ β _ v hv
  refine ⟨inferInstance, ?_, ?_⟩
  · simpa only [id_eq] using
      (indepFun_prod (μ := ν) (ν := β) hv (measurable_id : Measurable (id : Bool → Bool)))
  · intro b
    have hevent : {i : Ω × Bool | i.2 = b} = (Set.univ : Set Ω) ×ˢ ({b} : Set Bool) := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff,
        true_and]
    unfold mP
    rw [hevent, Measure.prod_prod, measure_univ, one_mul]

end

end AronowAudit.P029.Wave1.RandomizedProbability
