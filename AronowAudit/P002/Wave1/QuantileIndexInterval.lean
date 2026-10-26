import AronowAudit.P002.Wave1.QuantileIndexIntervalBlueprint
import AronowAudit.P002.Wave1.AlgorithmSupport.N2
import AronowAudit.P002.Wave1.AlgorithmSupport.N3
import AronowAudit.P002.Wave1.AlgorithmSupport.N4

/-! # Paper-domain theorem for P002: QuantileIndexInterval -/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem quantile_index_interval_paper :
  ∀ (M : ℕ) (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ),
    0 < M → (0 < α ∧ α < 1) → DataGeneratedCoefficients Qf Qg →
    ARRegular Qf → (∀ m, ARRegular (Qg m)) →
    ∀ (l u : EReal), l < u →
    (∀ β ∈ openInterval l u, ¬ crossing (fun m => arFunction (Qg m)) β) →
    let g := fun m => arFunction (Qg m)
    (∀ x ∈ openInterval l u, ∀ y ∈ openInterval l u,
      mcIndices g α x = mcIndices g α y) ∧
    (∀ x ∈ openInterval l u, ∀ a b : ℝ,
      l = (a : EReal) → u = (b : EReal) →
      mcIndices g α x ⊆ mcIndices g α a ∧
      mcIndices g α x ⊆ mcIndices g α b) ∧
    (∀ x ∈ openInterval l u, ∀ b : ℝ, l = ⊥ → u = (b : EReal) →
      mcIndices g α x ⊆ mcIndices g α b) ∧
    (∀ x ∈ openInterval l u, ∀ a : ℝ, u = ⊤ → l = (a : EReal) →
      mcIndices g α x ⊆ mcIndices g α a) := by
  exact AronowAudit.P002.Wave1.QuantileIndexInterval.assemble
    AlgorithmSupport.n2_proof AlgorithmSupport.n3_proof AlgorithmSupport.n4_proof

end
end AronowAudit.P002.Wave1
