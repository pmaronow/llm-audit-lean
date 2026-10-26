import AronowAudit.P045.Wave1.ClusterSamplerBlueprint
import AronowAudit.P045.Wave1.ClusterSampler.N1
import AronowAudit.P045.Wave1.ClusterSampler.N2
import AronowAudit.P045.Wave1.ClusterSampler.N3
import AronowAudit.P045.Wave1.ClusterSampler.N4
import AronowAudit.P045.Wave1.ClusterSampler.N5
import AronowAudit.P045.Wave1.ClusterSampler.N6
import AronowAudit.P045.Wave1.ClusterSampler.N7
import AronowAudit.P045.Wave1.ClusterSampler.N8

/-!
P045-T29: a counterexample to the documented cluster-sampler law.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

theorem cluster_sampler_as_documented_refuted :
    ¬ ∀ {n : ℕ}, 0 < n → ∀ (G : SimpleGraph (Fin n)) (p : ℝ), 0 ≤ p → p ≤ 1 →
      (∑ S : Finset (Fin n), terminalCentres G.edist 3 true S) = 1 ∧
      prob (terminalCentres G.edist 3 true) (epsilonNet G.edist 3) = 1 ∧
      (∀ z : Assignment n, clusteredTreatment G.edist true p z =
        ∑ S : Finset (Fin n), terminalCentres G.edist 3 true S * clusterProb G.edist S p z) := by
  exact AronowAudit.P045.Wave1.ClusterSampler.assemble
    AronowAudit.P045.Wave1.ClusterSampler.n1_proof
    AronowAudit.P045.Wave1.ClusterSampler.n2_proof
    AronowAudit.P045.Wave1.ClusterSampler.n3_proof
    AronowAudit.P045.Wave1.ClusterSampler.n4_proof
    AronowAudit.P045.Wave1.ClusterSampler.n5_proof
    AronowAudit.P045.Wave1.ClusterSampler.n6_proof
    AronowAudit.P045.Wave1.ClusterSampler.n7_proof
    AronowAudit.P045.Wave1.ClusterSampler.n8_proof

end

end AronowAudit.P045.Wave1
