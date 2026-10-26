import AronowAudit.P029.Wave1.IgnorabilityAllProfilesBlueprint
import AronowAudit.P029.Wave1.FiniteMeasure.N1
import AronowAudit.P029.Wave1.FiniteMeasure.N2
import AronowAudit.P029.Wave1.FiniteMeasure.N3
import AronowAudit.P029.Wave1.IgnorabilityAllProfiles.N1
import AronowAudit.P029.Wave1.IgnorabilityAllProfiles.N2

namespace AronowAudit.P029.Wave1

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

theorem printed_ignorability_ordering_all_profiles_refuted :
  ¬ (∀ {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
      [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X]
      (μX : Measure X) [IsProbabilityMeasure μX] (κ : Kernel X Ω) [IsMarkovKernel κ]
      (U : Ω → PotentialUnit X) (e : ℝ), 0 < e → e < 1 →
      (∀ x ∈ μX.support, ∀ᵐ ω ∂κ x, (U ω).x = x) →
      IVAssumptions (kernelPopulationLaw μX κ e) (kernelPopulationUnit U) Prod.snd →
      ∀ (x : X), x ∈ μX.support →
      Integrable (fun ω => (U ω).y0) (κ x) →
      Integrable (fun ω => (U ω).y1) (κ x) →
      0 < mP (κ x) {ω | (U ω).complier} →
      typicalAt ((κ x).prod (bernoulliMeasure e)) (liftUnit U) Prod.snd x →
      (∫ ω, (U ω).tau ∂κ x) = mCE (κ x) (fun ω => (U ω).tau) {ω | (U ω).complier}) := by
  exact IgnorabilityAllProfiles.assemble
    FiniteMeasure.n1_proof
    FiniteMeasure.n2_proof
    FiniteMeasure.n3_proof
    IgnorabilityAllProfiles.n1_proof
    IgnorabilityAllProfiles.n2_proof

end

end AronowAudit.P029.Wave1
