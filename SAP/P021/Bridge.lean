import SAP.P021.Defs
import AronowAudit.P021.P021_RDS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P021.Bridge

open MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section

variable {B : ℝ} {K : ℕ}

/-- The state spaces have the same bounded coordinate and discrete coordinates. -/
theorem state_eq : RDSState B K = AronowAudit.P021.RDSState B K := rfl

theorem outcome_eq (x : RDSState B K) : outcome x = AronowAudit.P021.outcome x := rfl

theorem degreeValue_eq (k : Fin K) : degreeValue k = AronowAudit.P021.degreeValue k := rfl

theorem populationMean_eq (F : Measure (RDSState B K)) :
    populationMean F = AronowAudit.P021.populationMean F := rfl

theorem samplingProbability_eq (F : Measure (RDSState B K)) (k : Fin K) :
    samplingProbability F k = AronowAudit.P021.samplingProbability F k := rfl

theorem ignorability_iff (F : Measure (RDSState B K)) :
    Ignorability F ↔ AronowAudit.P021.Ignorability F := Iff.rfl

theorem knownSampling_iff (F : Measure (RDSState B K)) (c : ℝ) (f : Fin K → ℝ) :
    KnownSampling F c f ↔ AronowAudit.P021.KnownSampling F c f := Iff.rfl

theorem empiricalAverage_eq {N : ℕ} (z : Fin N → RDSState B K)
    (g : RDSState B K → ℝ) :
    empiricalAverage z g = AronowAudit.P021.empiricalAverage z g := rfl

theorem sampleSet_eq {N : ℕ} (z : Fin N → RDSState B K) :
    sampleSet z = AronowAudit.P021.sampleSet z := rfl

theorem vhEstimator_eq {N : ℕ} (z : Fin N → RDSState B K) :
    vhEstimator z = AronowAudit.P021.vhEstimator z := rfl

theorem empiricalWeak_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Measure (RDSState B K)) (N : ℕ → ℕ)
    (z : (r : ℕ) → Ω → Fin (N r) → RDSState B K) :
    EmpiricalWeakInProbability P F N z ↔
      AronowAudit.P021.EmpiricalWeakInProbability P F N z := Iff.rfl

/-- Every component exported by the credited proposition has the same meaning. -/
theorem proposition_one_correspondence (F : Measure (RDSState B K))
    (c : ℝ) (f : Fin K → ℝ) :
    (0 < sampleFraction F ∧ degreeSupport F = observedSupport F ∧ c ≠ 0 ∧
      (∀ k ∈ degreeSupport F, 0 < c * f k ∧ f k ≠ 0 ∧
        degreeMass F k = (sampleFraction F / c) * (observedDegreeMass F k / f k)) ∧
      (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k) = c / sampleFraction F ∧
      (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k) ≠ 0 ∧
      populationMean F =
        (∑ k ∈ degreeSupport F, sampledMean F k * (observedDegreeMass F k / f k)) /
          (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k)) ↔
    (0 < AronowAudit.P021.sampleFraction F ∧
      AronowAudit.P021.degreeSupport F = AronowAudit.P021.observedSupport F ∧ c ≠ 0 ∧
      (∀ k ∈ AronowAudit.P021.degreeSupport F, 0 < c * f k ∧ f k ≠ 0 ∧
        AronowAudit.P021.degreeMass F k = (AronowAudit.P021.sampleFraction F / c) *
          (AronowAudit.P021.observedDegreeMass F k / f k)) ∧
      (∑ k ∈ AronowAudit.P021.degreeSupport F,
        AronowAudit.P021.observedDegreeMass F k / f k) = c / AronowAudit.P021.sampleFraction F ∧
      (∑ k ∈ AronowAudit.P021.degreeSupport F,
        AronowAudit.P021.observedDegreeMass F k / f k) ≠ 0 ∧
      AronowAudit.P021.populationMean F =
        (∑ k ∈ AronowAudit.P021.degreeSupport F, AronowAudit.P021.sampledMean F k *
          (AronowAudit.P021.observedDegreeMass F k / f k)) /
          (∑ k ∈ AronowAudit.P021.degreeSupport F,
            AronowAudit.P021.observedDegreeMass F k / f k)) := Iff.rfl

end
end SAP.P021.Bridge
