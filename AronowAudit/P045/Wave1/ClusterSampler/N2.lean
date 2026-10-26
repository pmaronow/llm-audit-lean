import AronowAudit.P045.Wave1.ClusterSamplerBlueprint

/-! P045-T29, node N2: enumerate the three nets, then sum an arbitrary law over them. -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.ClusterSampler

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

theorem n2_proof : N2 := by
  intro T
  have hnets : (univ : Finset (Finset (Fin 4))).filter
      (epsilonNet (pathDistance (n := 4)) 3) = {{1}, {2}, {0, 3}} := by
    decide
  have h1 : ({1} : Finset (Fin 4)) ∉
      ({{2}, {0, 3}} : Finset (Finset (Fin 4))) := by decide
  have h2 : ({2} : Finset (Fin 4)) ∉
      ({{0, 3}} : Finset (Finset (Fin 4))) := by decide
  classical
  unfold prob expect
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hnets, Finset.sum_insert h1,
    Finset.sum_insert h2, Finset.sum_singleton]
  exact (add_assoc _ _ _).symm

end

end AronowAudit.P045.Wave1.ClusterSampler
