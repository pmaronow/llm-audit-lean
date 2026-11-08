import AronowAudit.P006.Wave1.CorrectedRankingBlueprint
import AronowAudit.P006.Wave1.CorrectedRanking.N1
import AronowAudit.P006.Wave1.CorrectedRanking.N2
import AronowAudit.P006.Wave1.CorrectedRanking.N3
import AronowAudit.P006.Wave1.CorrectedRanking.N4
import AronowAudit.P006.Wave1.CorrectedRanking.N5
import AronowAudit.P006.Wave1.CorrectedRanking.N6

set_option autoImplicit false
universe u v
namespace AronowAudit.P006.Wave1
open AronowAudit.P006 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
noncomputable section

/-- Wave 1 completion of CorrectedRanking; the statement is written out in full. -/
theorem corrected_ranking_measurable :
  ∀ {K : ℕ} {C : Type u} [MeasurableSpace C] {Ω : Fin K → Type v}
    [∀ k, MeasurableSpace (Ω k)]
    (nk : Fin K → ℕ) (E : (k : Fin K) → Experiment (Ω k) C (nk k))
    (P0 : Measure C) (_hP0 : IsProbabilityMeasure P0)
    (_hS : ∀ k, Standing (E k))
    (_hmu0 : ∀ j k, (E j).μ0 = (E k).μ0)
    (_hac : ∀ k, P0 ≪ (E k).PX)
    (_hτ : ∀ k, Integrable (E k).τ P0)
    (_hU : ∀ k, TreatedUnbiased (E k) (E k).μ0 {π | Admissible π})
    (_hreward : ∀ k π, Admissible π → ∀ i,
      Integrable (fun ω => ((E k).observed π ω i -
        (E k).μhat π ω ((E k).X i ω)) * bit ((E k).T π i ω) *
        referenceWeight (nk k) P0 (E k).PX ((E k).X i ω)) ((E k).law π)),
    (∀ k π, Admissible π →
      (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX) π =
        (nk k : ℝ)*(∫ x, (E k).τ x*π x*
          referenceWeight (nk k) P0 (E k).PX x ∂(E k).PX) ∧
      (nk k : ℝ)*(∫ x, (E k).τ x*π x*
          referenceWeight (nk k) P0 (E k).PX x ∂(E k).PX) =
        (∫ x, (E k).τ x*π x ∂P0)) ∧
    (∀ k, IsBest {π | Admissible π}
      ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
      (positiveRule (E k).τ) ∧
      bestValue {π | Admissible π}
        ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX)) =
        (∫ x, positivePart ((E k).τ x) ∂P0)) ∧
    UniformRankPreservation (fun _ => {π | Admissible π})
      (fun k => (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
      (fun k => (E k).τ) ∧
    ((∀ k x, 0 ≤ (E k).τ x) →
      (∀ k, bestValue {π | Admissible π}
        ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX)) =
        (∫ x, (E k).τ x ∂P0)) ∧
      RelativeRankPreservation P0 (fun _ => {π | Admissible π})
        (fun k => (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
        (fun k => (E k).τ)) :=
  CorrectedRanking.assemble
    CorrectedRanking.n1_proof CorrectedRanking.n2_proof CorrectedRanking.n3_proof CorrectedRanking.n4_proof CorrectedRanking.n5_proof CorrectedRanking.n6_proof

example : CorrectedRanking.Target.{u, v} := corrected_ranking_measurable

end
end AronowAudit.P006.Wave1
