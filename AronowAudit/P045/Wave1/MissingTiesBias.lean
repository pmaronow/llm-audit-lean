import AronowAudit.P045.Wave1.MissingTiesBiasBlueprint
import AronowAudit.P045.Wave1.MissingTiesBias.N1
import AronowAudit.P045.Wave1.MissingTiesBias.N2
import AronowAudit.P045.Wave1.MissingTiesBias.N3
import AronowAudit.P045.Wave1.MissingTiesBias.N4
import AronowAudit.P045.Wave1.MissingTiesBias.N5
import AronowAudit.P045.Wave1.MissingTiesBias.N6

/-! Final assembly of the MissingTiesBias refutation. The statement below is the
literal body of the blueprint's Target, not an abbreviation for it. -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1

open AronowAudit.P045 Finset
open scoped BigOperators

/-- Refutation of the exact frozen contract, from the blueprint nodes. -/
theorem missing_ties_bias_as_printed_refuted :
  ¬ ∀ {n : ℕ}, 0 < n → ∀ (p : Design (Assignment n)) (A : Network n)
    (y : Fin n → Exposure → ℝ) (k : Exposure), k ≠ .d00 →
    ((∀ i, 0 < exposureProb p.mass (exposure A.adj) i k ∧
      0 < exposureProb p.mass (exposure A.adj) i .d00) →
      deletionRatiosDefined p.mass A y k .d00 0 →
      randomDeletionMean p.mass A y k .d00 0=effect y k .d00) ∧
    (∀ d₁ d₂ : ℕ, d₁ ≤ d₂ → d₂ ≤ (networkEdges A).card →
      deletionRatiosDefined p.mass A y k .d00 d₁ → deletionRatiosDefined p.mass A y k .d00 d₂ →
      |randomDeletionMean p.mass A y k .d00 d₁-effect y k .d00| ≤
        |randomDeletionMean p.mass A y k .d00 d₂-effect y k .d00|) := by
  exact MissingTiesBias.assemble
    MissingTiesBias.n1_proof
    MissingTiesBias.n2_proof
    MissingTiesBias.n3_proof
    MissingTiesBias.n4_proof
    MissingTiesBias.n5_proof
    MissingTiesBias.n6_proof

example : AronowAudit.P045.Wave1.MissingTiesBias.Target := missing_ties_bias_as_printed_refuted

end AronowAudit.P045.Wave1
