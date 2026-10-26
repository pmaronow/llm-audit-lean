import AronowAudit.P002.Wave1.Gap.RepairT21
import AronowAudit.P002.Wave1.Lib.FinitePopulationCLT

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem corrected_theorem7_limsup
    (k : ℕ) (δ e A B r α : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hα : 0 < α ∧ α < 1) :
    ∃ u : ℝ≥0∞,
      Tendsto (fun κ : ℝ => Filter.limsup
        (fun n : ℕ => supAdjustedTail n k δ e A B r α κ) atTop)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds u) ∧
      u ≤ ENNReal.ofReal α := by
  exact corrected_theorem7_limsup_of_finitePopulationCLT finitePopulationCLT
    k δ e A B r α hk hδ he hA hB hr hα

end
end AronowAudit.P002.Wave1
