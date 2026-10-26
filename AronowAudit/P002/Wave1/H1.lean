import AronowAudit.P002.Wave1.H1Blueprint
import AronowAudit.P002.Wave1.AlgorithmSupport.N2
import AronowAudit.P002.Wave1.AlgorithmSupport.N3
import AronowAudit.P002.Wave1.AlgorithmSupport.N4
import AronowAudit.P002.Wave1.AlgorithmSupport.N5
import AronowAudit.P002.Wave1.AlgorithmSupport.N6

/-! # Paper-domain theorem for P002: H1 -/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem H1_paper :
  ∀ (M : ℕ) (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ),
    0 < M → (0 < α ∧ α < 1) → DataGeneratedCoefficients Qf Qg →
    ARRegular Qf → (∀ m, ARRegular (Qg m)) →
    ∀ (J : List ℝ) (pieces : List (RecordedPiece M)), J ≠ [] →
    Algorithm1Run (fun m => arFunction (Qg m)) α J pieces →
    let f := arFunction Qf
    let g := fun m => arFunction (Qg m)
    ∀ p ∈ pieces,
      (∀ β ∈ closedInterval p.left p.right,
        p.index ∈ mcIndices g α β ∧
        g p.index β = (mcCritical g α β) ^ 2) ∧
      pieceSet f g p = mcSet f g α ∩ closedInterval p.left p.right := by
  exact AronowAudit.P002.Wave1.H1.assemble
    AlgorithmSupport.n2_proof AlgorithmSupport.n3_proof AlgorithmSupport.n4_proof
    AlgorithmSupport.n5_proof AlgorithmSupport.n6_proof

end
end AronowAudit.P002.Wave1
