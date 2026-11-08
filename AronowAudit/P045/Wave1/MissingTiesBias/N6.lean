import AronowAudit.P045.Wave1.MissingTiesBiasBlueprint

/-! True-network positivity at the zero-deletion witness (node N6). -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.MissingTiesBias

open AronowAudit.P045 Finset

/-- The printed degrees lie between one and six, so both exposure events have mass. -/
theorem n6_proof : N6 := by
  intro hN2 i
  have hdelete : deleteNetwork printedNetwork ∅ = printedNetwork.adj := by
    funext j k
    simp [deleteNetwork]
  have hp := hN2 ∅ i
  rw [hdelete] at hp
  have hb := zero_deletion_hajek_counterexample.2.2.1 i
  have hlo : (1 : ℝ) ≤ (measuredDegree ∅ i : ℝ) := by exact_mod_cast hb.1
  have hhi : (measuredDegree ∅ i : ℝ) ≤ 6 := by exact_mod_cast hb.2
  rw [hp.1, hp.2]
  exact ⟨div_pos (by linarith) (by norm_num), div_pos (by linarith) (by norm_num)⟩

end AronowAudit.P045.Wave1.MissingTiesBias
