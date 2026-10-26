import AronowAudit.P001.Wave1.TotalProbabilityCountableBlueprint
import AronowAudit.P001.Wave1.TotalProbabilityCountable.N1

namespace AronowAudit.P001.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableP001cFinalTotalProbabilityCountable (p : Prop) : Decidable p := Classical.propDecidable p

theorem total_probability_complete_correction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hne : ∀ i, (A i).Nonempty)
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcover : (⋃ i, A i) = Set.univ) (B : Set Ω) (hB : MeasurableSet B) :
    (prob μ B = ∑' i, prob μ (B ∩ A i)) ∧
    ((∀ i, 0 < prob μ (A i)) →
      prob μ B = ∑' i, (prob μ (B ∩ A i) / prob μ (A i)) * prob μ (A i)) ∧
    (∀ C : Set Ω, MeasurableSet C →
      ((C.Nonempty ∧ Cᶜ.Nonempty) ↔ C ≠ ∅ ∧ C ≠ Set.univ) ∧
      prob μ B = prob μ (B ∩ C) + prob μ (B ∩ Cᶜ)) ∧
    (0 ≤ prob μ (∅ : Set Ω) ∧ ¬ 0 < prob μ (∅ : Set Ω)) :=
  TotalProbabilityCountable.assemble TotalProbabilityCountable.n1_proof μ A hA hne hdis hcover B hB

end
end AronowAudit.P001.Wave1
