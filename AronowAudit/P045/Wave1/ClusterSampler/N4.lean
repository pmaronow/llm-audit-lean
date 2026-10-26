import AronowAudit.P045.Wave1.ClusterSamplerBlueprint

/-! P045-T29, node N4: the three non-retry terminating traces. -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.ClusterSampler

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

theorem n4_proof : N4 := by
  have ht1 :
      (∀ k : Fin ([1] : List (Fin 4)).length,
        marked (pathDistance (n := 4)) 3 ([1].take k.val).toFinset ≠ univ) ∧
      marked (pathDistance (n := 4)) 3 [1].toFinset = univ := by decide
  have ht2 :
      (∀ k : Fin ([2] : List (Fin 4)).length,
        marked (pathDistance (n := 4)) 3 ([2].take k.val).toFinset ≠ univ) ∧
      marked (pathDistance (n := 4)) 3 [2].toFinset = univ := by decide
  have ht30 :
      (∀ k : Fin ([3, 0] : List (Fin 4)).length,
        marked (pathDistance (n := 4)) 3 ([3, 0].take k.val).toFinset ≠ univ) ∧
      marked (pathDistance (n := 4)) 3 [3, 0].toFinset = univ := by decide
  have hR : (univ : Finset (Fin 4)) \ marked pathDistance 3 {3} = {0} := by decide
  have hc30 : centreDraw (pathDistance (n := 4)) 3 true {3} 0 = 1 := by
    norm_num [centreDraw, hR]
  have hc1 : centreDraw (pathDistance (n := 4)) 3 true ∅ 1 = 1/4 :=
    (four_path_coded_draws (1 : Fin 4)).1
  have hc2 : centreDraw (pathDistance (n := 4)) 3 true ∅ 2 = 1/4 :=
    (four_path_coded_draws (2 : Fin 4)).1
  have hc3 : centreDraw (pathDistance (n := 4)) 3 true ∅ 3 = 1/4 :=
    (four_path_coded_draws (3 : Fin 4)).1
  refine ⟨?_, ?_, ?_⟩
  · unfold traceMass
    rw [if_pos ht1]
    simpa [Fin.prod_univ_succ] using hc1
  · unfold traceMass
    rw [if_pos ht2]
    simpa [Fin.prod_univ_succ] using hc2
  · unfold traceMass
    rw [if_pos ht30]
    simpa [Fin.prod_univ_succ, hc3, hc30] using
      (show (1/4 : ℝ) * 1 = 1/4 by norm_num)

end

end AronowAudit.P045.Wave1.ClusterSampler
