import AronowAudit.P045.Wave1.MissingTiesBiasBlueprint

/-! Single-treated support and expectation, for node N1 of P045-T28. -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.MissingTiesBias

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

lemma subsetAssignment_singleton (t : Fin 10) :
    subsetAssignment 10 {t} = unitAssignment t := by
  funext i
  change decide (i ∈ ({t} : Finset (Fin 10))) = decide (i = t)
  simp

/-- Reindex complete randomization by the unique treated unit. -/
theorem n1_proof : N1 := by
  classical
  constructor
  · intro F
    rw [cr_subset_average, Finset.powersetCard_one]
    -- The singleton embedding has no duplicates and preserves cardinality.
    simpa only [average, Finset.sum_map, Finset.card_map,
      Function.Embedding.coeFn_mk, subsetAssignment_singleton,
      mean, Finset.card_univ, Fintype.card_fin]
  · intro z hz
    have hzmem : z ∈ fixedAssignments 10 1 := by
      by_contra hnot
      have hzero : crMass 10 1 z = 0 := by
        simp only [crMass, if_neg hnot]
      rw [hzero] at hz
      exact (lt_irrefl (0 : ℝ)) hz
    rw [fixed_assignments_map] at hzmem
    obtain ⟨S, hS, hzS⟩ := Finset.mem_map.mp hzmem
    have hcard : S.card = 1 := (Finset.mem_powersetCard.mp hS).2
    obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcard
    change subsetAssignment 10 {t} = z at hzS
    exact ⟨t, hzS.symm.trans (subsetAssignment_singleton t)⟩

end

end AronowAudit.P045.Wave1.MissingTiesBias
