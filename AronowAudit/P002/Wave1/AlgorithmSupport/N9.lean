import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Choose an admissible index independently at each prescribed gap sample. -/
theorem n9_proof : N9 := by
  classical
  intro M g α J hJ hall
  let select : ℝ → Fin M := fun β => Classical.choose (hall β)
  have hselect (β : ℝ) : select β ∈ mcIndices g α β :=
    Classical.choose_spec (hall β)
  let makePiece : EReal × EReal → RecordedPiece M :=
    fun lu => ⟨lu.1, lu.2, select (gapSample lu.1 lu.2)⟩
  refine ⟨(gapEndpoints J).map makePiece, hJ, ?_, ?_⟩
  · simp only [List.map_map, Function.comp_def, makePiece, Prod.mk.eta, List.map_id']
  · intro p hp
    obtain ⟨lu, _hlu, hpiece⟩ := List.mem_map.mp hp
    subst p
    exact hselect (gapSample lu.1 lu.2)

end
end AronowAudit.P002.Wave1.AlgorithmSupport
