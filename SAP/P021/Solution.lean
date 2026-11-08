import SAP.P021.Defs
import SAP.P021.Bridge
import AronowAudit.P021.P021_RDS
import SAP.P021.WH.W1.Proofs.T2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology
open scoped BigOperators

namespace SAP.P021

theorem T1 : T1Statement := by
  classical
  intro B K F hF c f hI hC
  have : IsProbabilityMeasure F := hF
  have h := (Bridge.proposition_one_correspondence F c f).mpr
    (AronowAudit.P021.proposition_one F c f
      ((Bridge.ignorability_iff F).mp hI) ((Bridge.knownSampling_iff F c f).mp hC))
  rcases h with ⟨hρ, hsupport, hc, hstrata, hden, hdenNZ, hmean⟩
  have hpos (k : Fin K) (hk : k ∈ degreeSupport F) : 0 < degreeMass F k := by
    simpa only [degreeSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hk
  have hmeans :
      (∑ k ∈ degreeSupport F, degreeMean F k * (observedDegreeMass F k / f k)) =
      (∑ k ∈ degreeSupport F, sampledMean F k * (observedDegreeMass F k / f k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [(hI k (hpos k hk)).1]
  have hnum :
      (∑ k ∈ degreeSupport F,
        degreeMean F k * (sampleFraction F / c) * (observedDegreeMass F k / f k)) =
      (sampleFraction F / c) *
        (∑ k ∈ degreeSupport F, degreeMean F k * (observedDegreeMass F k / f k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hscaledDen :
      (∑ k ∈ degreeSupport F, (sampleFraction F / c) * (observedDegreeMass F k / f k)) =
      (sampleFraction F / c) * (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k) :=
    (Finset.mul_sum _ _ _).symm
  have hcancel :
      (∑ k ∈ degreeSupport F,
        degreeMean F k * (sampleFraction F / c) * (observedDegreeMass F k / f k)) /
        (∑ k ∈ degreeSupport F,
          (sampleFraction F / c) * (observedDegreeMass F k / f k)) =
      (∑ k ∈ degreeSupport F, degreeMean F k * (observedDegreeMass F k / f k)) /
        (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k) := by
    rw [hnum, hscaledDen]
    field_simp [div_ne_zero hρ.ne' hc, hdenNZ]
  refine ⟨hρ, hsupport, hc, ?_, hden, hdenNZ, hmean, ?_, hcancel⟩
  · intro k hk
    have hp := hpos k hk
    have hs : 0 < sampledMass F k :=
      (div_pos_iff_of_pos_right hp).mp (hI k hp).2
    refine ⟨hs, (hstrata k hk).1, (hstrata k hk).2.1, ?_, (hstrata k hk).2.2⟩
    change degreeMass F k =
      (sampledMass F k / sampleFraction F) * sampleFraction F /
        (sampledMass F k / degreeMass F k)
    field_simp [hρ.ne', hp.ne', hs.ne']
  · rw [hcancel, hmeans]
    exact hmean

theorem T2 : SAP.P021.T2WholeStatement := SAP.P021.WH.W1.T2_whole

end SAP.P021
