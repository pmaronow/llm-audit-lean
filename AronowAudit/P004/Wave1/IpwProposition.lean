import AronowAudit.P004.Wave1.IpwPropositionBlueprint
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

theorem printed_ipw_proposition_refuted :
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
      LittleOp p (fun N z => augmented (p N) (R N) (g N) z-fittedIPW (R N) (O N) (θhat N) z)
        (fun N => (Real.sqrt N)⁻¹) ∧
      (∀ᶠ N in atTop, variance (p N) (augmented (p N) (R N) (g N)) =
        printedVarianceFormula (p N) (R N) (B N) (g N)) ∧
      (Nondegenerate (fun N => variance (p N) (augmented (p N) (R N) (g N))) →
        NormalLimit p (fun N z => (fittedIPW (R N) (O N) (θhat N) z-ame (p N) (R N)) /
          Real.sqrt (variance (p N) (augmented (p N) (R N) (g N)))))) := by
  exact AronowAudit.P004.Wave1.IpwProposition.assemble
    LinePopulation.n3_proof LinePopulation.n4_proof LinePopulation.n5_proof
    LinePopulation.n6_proof LinePopulation.n7_proof
    pw1_proof pw2_proof pw3_proof pw4_proof pw5_proof pw6_proof
    pw7_proof pw8_proof pw9_proof pw10_proof pw11_proof

end
end AronowAudit.P004.Wave1
