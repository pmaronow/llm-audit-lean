import AronowAudit.P027.Wave1.AePartitionBlueprint
import AronowAudit.P027.Wave1.AePartition.N1
import AronowAudit.P027.Wave1.AePartition.N2
import AronowAudit.P027.Wave1.AePartition.N3
import AronowAudit.P027.Wave1.AePartition.N4
import AronowAudit.P027.Wave1.AePartition.N5

namespace AronowAudit.P027.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P027
attribute [local instance] Classical.propDecidable

/-- Probability-zero disagreement within nonempty groups preserves the HT total
and variance estimator on the support, the actual variance, and `A`. -/
theorem aggregation_ae_partition_bridge :
    ∀ {G Ω : Type} [Fintype G] [Fintype Ω]
      (n : G → ℕ) (hn : ∀ g, 0 < n g)
      (D : Design (Σ g, Fin (n g)) Ω), Positive D →
      (∀ (g : G) (i j : Fin (n g)),
        expect D (fun ω =>
          if D.selected ω ⟨g,i⟩ = D.selected ω ⟨g,j⟩ then 0 else 1) = 0) →
      ∀ (y : (Σ g, Fin (n g)) → ℝ),
      let Dc : Design G Ω :=
        { weight := D.weight
          nonneg := D.nonneg
          total := D.total
          selected := fun ω g => D.selected ω ⟨g,⟨0, hn g⟩⟩ }
      Positive Dc ∧
      (∀ (g : G) (i : Fin (n g)), pi D ⟨g,i⟩ = pi Dc g) ∧
      (∀ (g h : G) (i : Fin (n g)) (j : Fin (n h)),
        joint D ⟨g,i⟩ ⟨h,j⟩ = joint Dc g h) ∧
      (∀ ω : Ω, 0 < D.weight ω →
        htTotal D y ω = htTotal Dc (groupTotal n y) ω ∧
        htVarianceEstimator D y ω =
          htVarianceEstimator Dc (groupTotal n y) ω) ∧
      variance D (htTotal D y) =
        variance Dc (htTotal Dc (groupTotal n y)) ∧
      biasA D y = biasA Dc (groupTotal n y) := by
  exact AronowAudit.P027.Wave1.AePartition.assemble
    AronowAudit.P027.Wave1.AePartition.n1_proof
    AronowAudit.P027.Wave1.AePartition.n2_proof
    AronowAudit.P027.Wave1.AePartition.n3_proof
    AronowAudit.P027.Wave1.AePartition.n4_proof
    AronowAudit.P027.Wave1.AePartition.n5_proof

end
end AronowAudit.P027.Wave1
