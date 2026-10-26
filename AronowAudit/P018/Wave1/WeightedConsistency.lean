import AronowAudit.P018.Wave1.WeightedConsistencyBlueprint
import AronowAudit.P018.Wave1.WeightedConsistency.G1
import AronowAudit.P018.Wave1.WeightedConsistency.G2
import AronowAudit.P018.Wave1.WeightedConsistency.G3
import AronowAudit.P018.Wave1.WeightedConsistency.G4
import AronowAudit.P018.Wave1.WeightedConsistency.G5
import AronowAudit.P018.Wave1.WeightedConsistency.G6
import AronowAudit.P018.Wave1.WeightedConsistency.G7
import AronowAudit.P018.Wave1.WeightedConsistency.G8
import AronowAudit.P018.Wave1.WeightedConsistency.M0
import AronowAudit.P018.Wave1.WeightedConsistency.M1
import AronowAudit.P018.Wave1.WeightedConsistency.M2
import AronowAudit.P018.Wave1.WeightedConsistency.M3
import AronowAudit.P018.Wave1.WeightedConsistency.M4
import AronowAudit.P018.Wave1.WeightedConsistency.M5
import AronowAudit.P018.Wave1.WeightedConsistency.M6
import AronowAudit.P018.Wave1.WeightedConsistency.M7
import AronowAudit.P018.Wave1.WeightedConsistency.M8
import AronowAudit.P018.Wave1.WeightedConsistency.M9
import AronowAudit.P018.Wave1.WeightedConsistency.M10
import AronowAudit.P018.Wave1.WeightedConsistency.M11

set_option autoImplicit false

namespace AronowAudit.P018.Wave1

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

/-- Weighted covariance-estimator consistency under the common directed kernel assumptions. -/
theorem weighted_consistency_common_directed_kernel :
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k),
    RepeatedStanding R → (∀ N d, R.T N d ≤ 2) →
    ∀ (X : U → U → Vec k) (Y : U → U → ℝ)
      (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool),
    (∀ N d, Function.Injective (dir N d)) →
    (∀ N d (t : Fin (R.T N d)) u₁ u₂,
      R.X N d t u₁ u₂ = (if dir N d t then X u₂ u₁ else X u₁ u₂) ∧
      R.Y N d t u₁ u₂ = (if dir N d t then Y u₂ u₁ else Y u₁ u₂)) →
    ∀ (w : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (a : ℕ → ℝ), (∀ N, 0 < a N) →
    (∃ C : ℝ, ∀ N d t, 0 < w N d t / a N ∧ w N d t / a N ≤ C) →
    ∀ (H : Mat k), H.PosDef →
    Tendsto (fun N : ℕ => recordWeightedH R (fun d t => w N d t / a N)) atTop (𝓝 H) →
    inProbability (repeatedLaw R) (fun N ω =>
      (N : ℝ) • recordWeightedVariance R (w N) ω - recordWeightedTarget R (w N)) :=
  WeightedConsistency.assemble
    WeightedConsistency.g1_proof
    WeightedConsistency.g2_proof
    WeightedConsistency.g3_proof
    WeightedConsistency.g4_proof
    WeightedConsistency.g5_proof
    WeightedConsistency.g6_proof
    WeightedConsistency.g7_proof
    WeightedConsistency.g8_proof
    WeightedConsistency.m0_proof
    WeightedConsistency.m1_proof
    WeightedConsistency.m2_proof
    WeightedConsistency.m3_proof
    WeightedConsistency.m4_proof
    WeightedConsistency.m5_proof
    WeightedConsistency.m6_proof
    WeightedConsistency.m7_proof
    WeightedConsistency.m8_proof
    WeightedConsistency.m9_proof
    WeightedConsistency.m10_proof
    WeightedConsistency.m11_proof

end
end AronowAudit.P018.Wave1
