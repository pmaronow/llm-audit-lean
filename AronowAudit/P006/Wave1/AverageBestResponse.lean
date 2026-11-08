import AronowAudit.P006.Wave1.AverageBestResponseBlueprint
import AronowAudit.P006.Wave1.BinaryExperiment.N1
import AronowAudit.P006.Wave1.BinaryExperiment.N2
import AronowAudit.P006.Wave1.BinaryExperiment.N3
import AronowAudit.P006.Wave1.BinaryExperiment.N4
import AronowAudit.P006.Wave1.BinaryExperiment.N5
import AronowAudit.P006.Wave1.AverageBestResponse.N1

set_option autoImplicit false
namespace AronowAudit.P006.Wave1
open AronowAudit.P006 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section

/-- Wave 1 completion of AverageBestResponse; the statement is written out in full. -/
theorem printed_average_best_response_refuted :
  ¬ ∀ {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] [Countable C]
      [MeasurableSingletonClass C] {n : ℕ} (E : Experiment Ω C n),
      Standing E → PointwiseUnbiased E {π | Admissible π} →
      IsBest {π | Admissible π} E.expectedATO (printedAverageRule E.μ1) ∧
      IsBest {π | Admissible π} E.expectedATT (printedAverageRule E.τ) :=
  AverageBestResponse.assemble
    BinaryExperiment.n1_proof BinaryExperiment.n2_proof BinaryExperiment.n3_proof BinaryExperiment.n4_proof BinaryExperiment.n5_proof AverageBestResponse.n1_proof

example : AverageBestResponse.Target := printed_average_best_response_refuted

/-- The explicit finite witness used by the universal refutation. -/
theorem printed_average_best_response_witness : AverageBestResponse.Witness :=
  AverageBestResponse.assemble_witness
    BinaryExperiment.n1_proof BinaryExperiment.n2_proof BinaryExperiment.n3_proof BinaryExperiment.n4_proof BinaryExperiment.n5_proof AverageBestResponse.n1_proof

end
end AronowAudit.P006.Wave1
