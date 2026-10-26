import AronowAudit.P022.Wave1.RandomizationVariance.N1
import AronowAudit.P022.Wave1.RandomizationVariance.N2
import AronowAudit.P022.Wave1.RandomizationVariance.N3
import AronowAudit.P022.Wave1.RandomizationVariance.N4
import AronowAudit.P022.Wave1.FixedArm.N1

set_option autoImplicit false
namespace AronowAudit.P022.Wave1
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem fixed_arm_variance_limit_eventually :
  ∀ (S : ExperimentSequence) (m k : ℕ),
    (∀ᶠ q : ℕ in atTop, (S.design q).m = m) →
    (∀ᶠ q : ℕ in atTop, (S.design q).k = k) →
    (∃ M : ℝ, ∀ q, finiteVariance (rowOutcomes S true q) ≤ M ∧
      finiteVariance (rowOutcomes S false q) ≤ M) →
    Tendsto (fun q => trueVariance (S.design q)
      (rowOutcomes S true q) (rowOutcomes S false q) -
      (finiteVariance (rowOutcomes S true q) / m +
       finiteVariance (rowOutcomes S false q) / k)) atTop (𝓝 0) := by
  exact FixedArm.assemble RandomizationVariance.n1_proof RandomizationVariance.n2_proof RandomizationVariance.n3_proof RandomizationVariance.n4_proof FixedArm.n1_proof

end
end AronowAudit.P022.Wave1
