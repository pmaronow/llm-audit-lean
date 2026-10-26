import AronowAudit.P002.Wave1.Algorithm2Blueprint
import AronowAudit.P002.Wave1.AlgorithmSupport.N1
import AronowAudit.P002.Wave1.AlgorithmSupport.N2
import AronowAudit.P002.Wave1.AlgorithmSupport.N3
import AronowAudit.P002.Wave1.AlgorithmSupport.N4
import AronowAudit.P002.Wave1.AlgorithmSupport.N5
import AronowAudit.P002.Wave1.AlgorithmSupport.N10
import AronowAudit.P002.Wave1.AlgorithmSupport.N11
import AronowAudit.P002.Wave1.AlgorithmSupport.N12
import AronowAudit.P002.Wave1.AlgorithmSupport.N13
import AronowAudit.P002.Wave1.AlgorithmSupport.N14

/-! # Paper-domain theorem for P002: Algorithm2 -/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem algorithm2_paper :
  ∀ (M : ℕ) (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ),
    0 < M → (0 < α ∧ α < 1) → DataGeneratedCoefficients Qf Qg →
    ARRegular Qf → (∀ m, ARRegular (Qg m)) →
    ∀ (J : List ℝ), IntersectionList (fun m => arFunction (Qg m)) J → J ≠ [] →
    let f := arFunction Qf
    let g := fun m => arFunction (Qg m)
    (∃ pieces, Algorithm2Run g α J pieces) ∧
    ∀ pieces, Algorithm2Run g α J pieces →
      pieces.length ≤ J.length + 1 ∧
      (pieces.map (fun p => p.right)).Pairwise (· < ·) ∧
      (∀ p ∈ pieces, p.right = ⊤ ∨
        ∃ e : ℝ, p.right = (e : EReal) ∧ e ∈ J) ∧
      (∀ β : ℝ, ∃ p ∈ pieces, β ∈ closedInterval p.left p.right) ∧
      (∀ p ∈ pieces, ∀ β ∈ closedInterval p.left p.right,
        p.index ∈ mcIndices g α β) ∧
      (∀ p ∈ pieces, pieceSet f g p =
        mcSet f g α ∩ closedInterval p.left p.right) ∧
      returnedSet f g pieces = mcSet f g α := by
  exact AronowAudit.P002.Wave1.Algorithm2.assemble
    AlgorithmSupport.n1_proof AlgorithmSupport.n2_proof AlgorithmSupport.n3_proof
    AlgorithmSupport.n4_proof AlgorithmSupport.n5_proof AlgorithmSupport.n10_proof
    AlgorithmSupport.n11_proof AlgorithmSupport.n12_proof AlgorithmSupport.n13_proof
    AlgorithmSupport.n14_proof

end
end AronowAudit.P002.Wave1
