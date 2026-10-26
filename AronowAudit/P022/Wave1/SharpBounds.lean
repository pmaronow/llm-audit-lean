import AronowAudit.P022.Wave1.RandomizationVariance.N1
import AronowAudit.P022.Wave1.RandomizationVariance.N2
import AronowAudit.P022.Wave1.RandomizationVariance.N3
import AronowAudit.P022.Wave1.RandomizationVariance.N4
import AronowAudit.P022.Wave1.SharpBounds.N1
import AronowAudit.P022.Wave1.SharpBounds.N2
import AronowAudit.P022.Wave1.SharpBounds.N3
import AronowAudit.P022.Wave1.SharpBounds.N4
import AronowAudit.P022.Wave1.SharpBounds.N5
import AronowAudit.P022.Wave1.SharpBounds.N6
import AronowAudit.P022.Wave1.SharpBounds.N7
import AronowAudit.P022.Wave1.SharpBounds.N8
import AronowAudit.P022.Wave1.SharpBounds.N9
import AronowAudit.P022.Wave1.SharpBounds.N10
import AronowAudit.P022.Wave1.SharpBounds.N11
import AronowAudit.P022.Wave1.SharpBounds.N12

set_option autoImplicit false
namespace AronowAudit.P022.Wave1
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem sharp_bounds_variance_and_all_couplings :
  ∀ (d : Design) (y1 y0 : Fin d.N → ℝ),
    designExpectation d (estimatedEffect d y1 y0) = averageEffect d y1 y0 ∧
    trueVariance d y1 y0 = varianceExpression d.N d.m d.k
      (finiteVariance y1) (finiteVariance y0) (finiteCovariance y1 y0) ∧
    (∀ z1 z0 : Fin d.N → ℝ,
      List.Perm (List.ofFn z1) (List.ofFn y1) →
      List.Perm (List.ofFn z0) (List.ofFn y0) →
      sharpCovariance y1 y0 .L ≤ finiteCovariance z1 z0 ∧
      finiteCovariance z1 z0 ≤ sharpCovariance y1 y0 .H ∧
      populationBound d y1 y0 .L ≤ trueVariance d z1 z0 ∧
      trueVariance d z1 z0 ≤ populationBound d y1 y0 .H) ∧
    trueVariance d (sortedValues y1) (sortedValues y0) =
      populationBound d y1 y0 .H ∧
    trueVariance d (sortedValues y1) (fun i => sortedValues y0 i.rev) =
      populationBound d y1 y0 .L ∧
    (∀ J ∈ empiricalCompatibleLaws y1 y0,
      Integrable (fun p : ℝ × ℝ => p.1 * p.2) (J : Measure (ℝ × ℝ)) ∧
      sharpCovariance y1 y0 .L ≤ lawCovariance J ∧
      lawCovariance J ≤ sharpCovariance y1 y0 .H) ∧
    (∀ B, ∃ J ∈ empiricalCompatibleLaws y1 y0,
      lawCovariance J = sharpCovariance y1 y0 B ∧
      ∀ f : BoundedContinuousFunction (ℝ × ℝ) ℝ,
        (∫ p, f p ∂(J : Measure (ℝ × ℝ))) =
          ∫ u in (0 : ℝ)..1,
            f (empiricalQuantile y1 u, empiricalQuantile y0
              (if B = BoundSide.H then u else 1 - u))) := by
  exact SharpBounds.assemble RandomizationVariance.n1_proof RandomizationVariance.n2_proof RandomizationVariance.n3_proof RandomizationVariance.n4_proof SharpBounds.n1_proof SharpBounds.n2_proof SharpBounds.n3_proof SharpBounds.n4_proof SharpBounds.n5_proof SharpBounds.n6_proof SharpBounds.n7_proof SharpBounds.n8_proof SharpBounds.n9_proof SharpBounds.n10_proof SharpBounds.n11_proof SharpBounds.n12_proof

end
end AronowAudit.P022.Wave1
