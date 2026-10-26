import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint
import Mathlib.Data.List.Zip

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Scan the chain until its right endpoint is above the given real point.
The lower-bound invariant is preserved without a sortedness hypothesis. -/
theorem n7_proof : N7 := by
  intro J β
  have haux : ∀ (L : List ℝ) (a : EReal), a ≤ (β : EReal) →
      ∃ lu ∈ (a :: L.map (fun x => (x : EReal))).zip
          (L.map (fun x => (x : EReal)) ++ [⊤]),
        β ∈ closedInterval lu.1 lu.2 := by
    intro L
    induction L with
    | nil =>
        intro a ha
        refine ⟨(a, (⊤ : EReal)), ?_, ?_⟩
        · change (a, (⊤ : EReal)) ∈ [(a, (⊤ : EReal))]
          exact List.mem_cons_self
        · exact ⟨ha, le_top⟩
    | cons b L ih =>
        intro a ha
        change ∃ lu ∈ (a, (b : EReal)) ::
            (((b : EReal) :: L.map (fun x => (x : EReal))).zip
              (L.map (fun x => (x : EReal)) ++ [⊤])),
          β ∈ closedInterval lu.1 lu.2
        rcases le_or_gt (β : EReal) (b : EReal) with hβb | hbβ
        · exact ⟨(a, (b : EReal)), List.mem_cons_self, ha, hβb⟩
        · obtain ⟨lu, hlu, hβ⟩ := ih (b : EReal) hbβ.le
          exact ⟨lu, List.mem_cons_of_mem _ hlu, hβ⟩
  exact haux J ⊥ bot_le

end
end AronowAudit.P002.Wave1.AlgorithmSupport
