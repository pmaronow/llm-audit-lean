import AronowAudit.P004.Wave1.IpwBoundCoverageBlueprint
import AronowAudit.P004.Wave1.LinePopulation.N3
import AronowAudit.P004.Wave1.LinePopulation.N4
import AronowAudit.P004.Wave1.LinePopulation.N5
import AronowAudit.P004.Wave1.LinePopulation.N6
import AronowAudit.P004.Wave1.LinePopulation.N7
import AronowAudit.P004.Wave1.PairedWitness.PW1
import AronowAudit.P004.Wave1.PairedWitness.PW2
import AronowAudit.P004.Wave1.PairedWitness.PW3
import AronowAudit.P004.Wave1.PairedWitness.PW4
import AronowAudit.P004.Wave1.PairedWitness.PW5
import AronowAudit.P004.Wave1.PairedWitness.PW6
import AronowAudit.P004.Wave1.PairedWitness.PW7
import AronowAudit.P004.Wave1.PairedWitness.PW8
import AronowAudit.P004.Wave1.PairedWitness.PW9
import AronowAudit.P004.Wave1.PairedWitness.PW10
import AronowAudit.P004.Wave1.PairedWitness.PW11

/-! Full-universal-closure refutation at universe zero, assembled from the
line-population guards and the exact paired-witness moments. -/

namespace AronowAudit.P004.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.PairedWitness
open scoped BigOperators

theorem printed_ipw_bound_and_literal_coverage_refuted :
  ¬ (∀ {Space : ℕ → Type} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
      {k : ℕ} (P : PopulationSequence Space)
      (O : ∀ N, Fin N → Fin k → ℝ) (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
      (θhat : ∀ N, Assignment N → Fin k → ℝ) (d h : ℝ)
      (_hd : 0 ≤ d) (_hh : 0 ≤ h) (_hP : SpatialLocalConditions P)
      (_hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
      (_hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
      (_hlog : LogisticConditions O θ₀ Θ θhat)
      (_hoverlap : Overlap (fun N => propensities (O N) θ₀)),
      let p := fun N => propensities (O N) θ₀
      let R := circleSequence P d
      let B := spatialNeighborhoods P h
      let g := fun N => printedFits (p N) (R N) (O N)
      ((∀ N, 0 ≤ printedHomophilyQ (p N) (R N) (B N) (g N)) →
        ∀ᶠ N in atTop, variance (p N) (augmented (p N) (R N) (g N)) ≤
          printedSecondMomentBound (p N) (R N) (B N) (g N)) ∧
      (Nondegenerate (fun N => variance (p N) (augmented (p N) (R N) (g N))) →
        ∀ α : ℝ, 0 < α → α < 1/2 →
        PrintedCoverage (fun N => prob (p N) (fun z =>
          let phat := propensities (O N) (θhat N z)
          let ghat := fun i a => dot (O N i) (fittedBeta phat (R N) (O N) a z)
          normalQuantile (α/2) ≤ |(hajek (R N) z-ame (p N) (R N))/
            Real.sqrt (printedSAH phat (R N) (B N) ghat z)| ∧
          |(hajek (R N) z-ame (p N) (R N))/Real.sqrt (printedSAH phat (R N) (B N) ghat z)| ≤
            normalQuantile (1-α/2))) α ∧
        ((∀ N, 0 ≤ printedHomophilyQ (p N) (R N) (B N) (g N)) →
          PrintedCoverage (fun N => prob (p N) (fun z =>
            let phat := propensities (O N) (θhat N z)
            let ghat := fun i a => dot (O N i) (fittedBeta phat (R N) (O N) a z)
            let V := (sandwich z (weightedEpsilon phat (R N) ghat z)
              (uniformDistanceKernel (nodeSeparation (P N)) h)) 1 1
            normalQuantile (α/2) ≤ |(hajek (R N) z-ame (p N) (R N))/Real.sqrt V| ∧
              |(hajek (R N) z-ame (p N) (R N))/Real.sqrt V| ≤ normalQuantile (1-α/2))) α))) := by
  exact AronowAudit.P004.Wave1.IpwBoundCoverage.assemble
    LinePopulation.n3_proof LinePopulation.n4_proof LinePopulation.n5_proof
    LinePopulation.n6_proof LinePopulation.n7_proof
    pw1_proof pw2_proof pw3_proof pw4_proof pw5_proof pw6_proof
    pw7_proof pw8_proof pw9_proof pw10_proof pw11_proof

end
end AronowAudit.P004.Wave1
