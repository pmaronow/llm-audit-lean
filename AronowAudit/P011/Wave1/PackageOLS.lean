import AronowAudit.P011.Wave1.PackageOLSBlueprint
import AronowAudit.P011.Wave1.PropositionOne.N1
import AronowAudit.P011.Wave1.PropositionOne.N2
import AronowAudit.P011.Wave1.PropositionOne.N3
import AronowAudit.P011.Wave1.PropositionOne.N4
import AronowAudit.P011.Wave1.PropositionOne.N5
import AronowAudit.P011.Wave1.PropositionOne.N6
import AronowAudit.P011.Wave1.PropositionOne.N7
import AronowAudit.P011.Wave1.PropositionOne.N8
import AronowAudit.P011.Wave1.PropositionOne.N9
import AronowAudit.P011.Wave1.PropositionOne.N10
import AronowAudit.P011.Wave1.CorollaryOne.N1
import AronowAudit.P011.Wave1.CorollaryOne.N3
import AronowAudit.P011.Wave1.PackageOLS.N1
import AronowAudit.P011.Wave1.PackageOLS.N2
import AronowAudit.P011.Wave1.PackageOLS.N3

set_option autoImplicit false

namespace AronowAudit.P011.Wave1

open AronowAudit.P011 AronowAudit.P011.Wave1.PropositionOne AronowAudit.P011.Wave1.CorollaryOne
  MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Matrix

noncomputable section

/-- Refutation of the printed generic OLS guarantee (P011-T35). -/
theorem printed_package_ols_guarantee_refuted :
  ¬ ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 → Valid F →
      ∀ (p : ℕ) (j : Fin p) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (b : Fin p → ℝ),
        (∀ k, ((D k)ᵀ * D k).det ≠ 0) → (∀ k, MeanModel (F.model k) (D k) b) →
        (∀ k i, (F.model k).theta i = olsTheta (D k) j i) →
        ∀ (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
          (∀ k y, Maximizes (F.model k).R (F.model k).d
            (fun B => V1 B (weighted (F.model k) y)) (A k y)) →
          Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) ∧
            PrintedConservativeCoverage F (fun k y => V1 (A k y) (weighted (F.model k) y)) := by
  exact AronowAudit.P011.Wave1.PackageOLS.assemble
    AronowAudit.P011.Wave1.PropositionOne.n1_proof
    AronowAudit.P011.Wave1.PropositionOne.n2_proof
    AronowAudit.P011.Wave1.PropositionOne.n3_proof
    AronowAudit.P011.Wave1.PropositionOne.n4_proof
    AronowAudit.P011.Wave1.PropositionOne.n5_proof
    AronowAudit.P011.Wave1.PropositionOne.n6_proof
    AronowAudit.P011.Wave1.PropositionOne.n7_proof
    AronowAudit.P011.Wave1.PropositionOne.n8_proof
    AronowAudit.P011.Wave1.PropositionOne.n9_proof
    AronowAudit.P011.Wave1.PropositionOne.n10_proof
    AronowAudit.P011.Wave1.CorollaryOne.n1_proof
    AronowAudit.P011.Wave1.CorollaryOne.n3_proof
    AronowAudit.P011.Wave1.PackageOLS.n1_proof
    AronowAudit.P011.Wave1.PackageOLS.n2_proof
    AronowAudit.P011.Wave1.PackageOLS.n3_proof

end

end AronowAudit.P011.Wave1
