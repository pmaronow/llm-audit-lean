import AronowAudit.P004.Wave1.ObservationalCoverageBlueprint
import AronowAudit.P004.Wave1.ObservationalCoverage.O1
import AronowAudit.P004.Wave1.ObservationalCoverage.O3
import AronowAudit.P004.Wave1.ObservationalCoverage.O4
import AronowAudit.P004.Wave1.ObservationalCoverage.O5
import AronowAudit.P004.Wave1.ObservationalCoverage.O9
import AronowAudit.P004.Wave1.ObservationalCoverage.O10
import AronowAudit.P004.Wave1.ObservationalCoverage.O11
import AronowAudit.P004.Wave1.ObservationalCoverage.O12
import AronowAudit.P004.Wave1.LinePopulation.N3
import AronowAudit.P004.Wave1.LinePopulation.N4
import AronowAudit.P004.Wave1.LinePopulation.N5
import AronowAudit.P004.Wave1.LinePopulation.N6
import AronowAudit.P004.Wave1.LinePopulation.N7
import AronowAudit.P004.Wave1.DesignLimits.DL8
import AronowAudit.P004.Wave1.DesignLimits.NF

/-! P004-T36: refutation of the full universal closure of the printed
observational-coverage assertion, at universe zero. -/

namespace AronowAudit.P004.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

theorem printed_observational_coverage_refuted :
    ¬ (∀ {Space : ℕ → Type} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
      {k : ℕ} (P : PopulationSequence Space)
      (O : ∀ N, Fin N → Fin k → ℝ) (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
      (θhat : ∀ N, Assignment N → Fin k → ℝ) (d h : ℝ)
      (_hd : 0 ≤ d) (_hh : 0 ≤ h) (_hP : SpatialLocalConditions P)
      (_hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
      (_hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
      (_hlog : LogisticConditions O θ₀ Θ θhat)
      (_hoverlap : Overlap (fun N => propensities (O N) θ₀))
      (_hv : Nondegenerate (fun N => variance (propensities (O N) θ₀)
        (augmented (propensities (O N) θ₀) (circleAverage (P N) d)
          (printedFits (propensities (O N) θ₀) (circleAverage (P N) d) (O N))))),
      ∀ α : ℝ, 0 < α → α < 1/2 → PrintedCoverage (fun N =>
        prob (propensities (O N) θ₀) (fun z =>
          let R := circleAverage (P N) d
          let phat := propensities (O N) (θhat N z)
          let g := fun i a => dot (O N i) (fittedBeta phat R (O N) a z)
          |fittedIPW R (O N) (θhat N) z-ame (propensities (O N) θ₀) R| ≤
            normalQuantile (1-α/2)*Real.sqrt (printedSAH phat R (spatialNeighborhoods P h N) g z))) α) := by
  exact ObservationalCoverage.assemble
    LinePopulation.n3_proof LinePopulation.n4_proof LinePopulation.n5_proof
    LinePopulation.n6_proof LinePopulation.n7_proof
    ObservationalCoverage.o1_proof ObservationalCoverage.o3_proof
    ObservationalCoverage.o4_proof ObservationalCoverage.o5_proof
    ObservationalCoverage.o11_proof ObservationalCoverage.o12_proof dl8_proof nf_proof

end
end AronowAudit.P004.Wave1
