import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint

/-!
# P002-T23: corrected (H.1) on every Algorithm 1 gap

Supplement p. 45, display (H.1), with the corrected square on the absolute critical value,
for the paper's data-generated AR coefficients under Assumptions 6/7.
`Algorithm1Run` contains the complete sorted intersection list and the prescribed gap
samples; no interval-wide validity is assumed.
-/

namespace AronowAudit.P002.Wave1.H1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Corrected (H.1) on every recorded Algorithm 1 gap. -/
def Target : Prop :=
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
      pieceSet f g p = mcSet f g α ∩ closedInterval p.left p.right

/-- The Algorithm 1 support statements imply the corrected gap formula. -/
theorem assemble (h2 : AlgorithmSupport.N2) (h3 : AlgorithmSupport.N3)
    (h4 : AlgorithmSupport.N4) (h5 : AlgorithmSupport.N5) (h6 : AlgorithmSupport.N6) :
    Target := by
  intro M Qf Qg α hM hα _hdata hQf hQg J pieces _hJ hRun
  have hreg := arFamily_regular Qg hQg
  have hf : ∀ β, 0 ≤ arFunction Qf β :=
    fun β => div_nonneg (hQf.2 β) (le_of_lt (hQf.1 β))
  exact AlgorithmSupport.glue_algorithm1_pieces h2 h3 h4 h5 h6 (arFunction Qf)
    (fun m => arFunction (Qg m)) α hM hα hreg.1 hreg.2.1 hf J pieces hRun

end
end AronowAudit.P002.Wave1.H1
