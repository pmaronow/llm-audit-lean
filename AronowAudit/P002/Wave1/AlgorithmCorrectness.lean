import AronowAudit.P002.Wave1.AlgorithmCorrectnessBlueprint
import AronowAudit.P002.Wave1.AlgorithmSupport.N1
import AronowAudit.P002.Wave1.AlgorithmSupport.N2
import AronowAudit.P002.Wave1.AlgorithmSupport.N3
import AronowAudit.P002.Wave1.AlgorithmSupport.N4
import AronowAudit.P002.Wave1.AlgorithmSupport.N5
import AronowAudit.P002.Wave1.AlgorithmSupport.N6
import AronowAudit.P002.Wave1.AlgorithmSupport.N7
import AronowAudit.P002.Wave1.AlgorithmSupport.N8
import AronowAudit.P002.Wave1.AlgorithmSupport.N9
import AronowAudit.P002.Wave1.AlgorithmSupport.N10
import AronowAudit.P002.Wave1.AlgorithmSupport.N11
import AronowAudit.P002.Wave1.AlgorithmSupport.N12
import AronowAudit.P002.Wave1.AlgorithmSupport.N13
import AronowAudit.P002.Wave1.AlgorithmSupport.N14

/-! # Paper-domain theorem for P002: AlgorithmCorrectness -/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem algorithm_correctness_paper :
  ∀ (M : ℕ) (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ),
    0 < M → (0 < α ∧ α < 1) → DataGeneratedCoefficients Qf Qg →
    ARRegular Qf → (∀ m, ARRegular (Qg m)) →
    let f := arFunction Qf
    let g := fun m => arFunction (Qg m)
    (∃ J, IntersectionList g J) ∧
    (∀ J, IntersectionList g J → ∃ pieces, Algorithm1Run g α J pieces) ∧
    (∀ J pieces, Algorithm1Run g α J pieces →
      returnedSet f g pieces = mcSet f g α) ∧
    (∀ J, IntersectionList g J → J ≠ [] →
      ∃ pieces, Algorithm2Run g α J pieces) ∧
    (∀ J pieces, Algorithm2Run g α J pieces →
      returnedSet f g pieces = mcSet f g α) ∧
    (∀ J, IntersectionList g J → J = [] →
      ∀ β m, m ∈ mcIndices g α β →
        {x | f x ≤ g m x} = mcSet f g α) := by
  exact AronowAudit.P002.Wave1.AlgorithmCorrectness.assemble
    AlgorithmSupport.n1_proof AlgorithmSupport.n2_proof AlgorithmSupport.n3_proof
    AlgorithmSupport.n4_proof AlgorithmSupport.n5_proof AlgorithmSupport.n6_proof
    AlgorithmSupport.n7_proof AlgorithmSupport.n8_proof AlgorithmSupport.n9_proof
    AlgorithmSupport.n10_proof AlgorithmSupport.n11_proof AlgorithmSupport.n12_proof
    AlgorithmSupport.n13_proof AlgorithmSupport.n14_proof

end
end AronowAudit.P002.Wave1
