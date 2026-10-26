import AronowAudit.P006.Wave1.TTAlignmentBlueprint
import AronowAudit.P006.Wave1.BinaryExperiment.N1
import AronowAudit.P006.Wave1.BinaryExperiment.N2
import AronowAudit.P006.Wave1.BinaryExperiment.N3
import AronowAudit.P006.Wave1.BinaryExperiment.N4
import AronowAudit.P006.Wave1.BinaryExperiment.N5
import AronowAudit.P006.Wave1.TTAlignment.N1
import AronowAudit.P006.Wave1.TTAlignment.N2

set_option autoImplicit false
namespace AronowAudit.P006.Wave1
open AronowAudit.P006 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section

/-- P006-T27: refutation of the printed TT alignment assertion. -/
theorem printed_TT_alignment_refuted :
  ¬ ∀ {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n),
      Standing E → ∀ (PiSet : Set (C → ℝ)), (∀ π ∈ PiSet, Admissible π) →
      PointwiseUnbiased E PiSet →
      (∀ π ∈ PiSet, E.expectedTT π = (n : ℝ) * E.V π) ∧
      (∀ π, IsBest PiSet E.expectedTT π ↔ IsBest PiSet E.V π) ∧
      (∀ π, IsBest PiSet E.expectedTT π → regret PiSet E.V π = 0) ∧
      (PiSet = {π | Admissible π} → IsBest PiSet E.expectedTT (positiveRule E.τ)) :=
  TTAlignment.assemble
    BinaryExperiment.n1_proof BinaryExperiment.n2_proof BinaryExperiment.n3_proof BinaryExperiment.n4_proof BinaryExperiment.n5_proof TTAlignment.n1_proof TTAlignment.n2_proof


end
end AronowAudit.P006.Wave1
