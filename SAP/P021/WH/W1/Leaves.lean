import SAP.P021.Defs.WholeW1
import SAP.P021.Bridge
import AronowAudit.P021.P021_RDS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P021.WH.W1

open MeasureTheory Filter Topology

/-- Both whole consistency conclusions follow from existing corollaries, which already
allow empty finite samples. All coordinate definitions agree through `SAP.P021.Bridge`.
There are no new mathematical leaves. -/
theorem T2_assembly : T2WholeStatement := by
  constructor
  · intro Ω _ B K P hP hB hK F hF N hN z hz hweak c a ha hI hC
    have : IsProbabilityMeasure P := hP
    have : IsProbabilityMeasure F := hF
    have h := AronowAudit.P021.corollary_one P hB hK F N hN z hz
      ((Bridge.empiricalWeak_iff P F N z).mp hweak) c a ha
      ((Bridge.ignorability_iff F).mp hI)
      ((Bridge.knownSampling_iff F c (fun k => a * degreeValue k)).mp hC)
    simpa only [Bridge.vhEstimator_eq, Bridge.populationMean_eq] using h
  · intro B K hB hK F hF N hN z hweak c a ha hI hC
    have : IsProbabilityMeasure F := hF
    have hw : ∀ g : RDSState B K → ℝ, Continuous g →
        Tendsto (fun r => AronowAudit.P021.empiricalAverage (z r) g) atTop
          (𝓝 (∫ x, g x ∂F)) := by
      simpa only [Bridge.empiricalAverage_eq] using hweak
    have h := AronowAudit.P021.corollary_one_deterministic hB hK F N hN z hw c a ha
      ((Bridge.ignorability_iff F).mp hI)
      ((Bridge.knownSampling_iff F c (fun k => a * degreeValue k)).mp hC)
    simpa only [Bridge.vhEstimator_eq, Bridge.populationMean_eq] using h

end SAP.P021.WH.W1
