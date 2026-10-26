import AronowAudit.P001.Wave1.IrrationalRangeBlueprint
import AronowAudit.P001.Wave1.IrrationalRange.N1
import AronowAudit.P001.Wave1.IrrationalRange.N2
import AronowAudit.P001.Wave1.IrrationalRange.N3
import AronowAudit.P001.Wave1.IrrationalRange.N4

namespace AronowAudit.P001.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableP001cFinalIrrationalRange (p : Prop) : Decidable p := Classical.propDecidable p

theorem continuous_range_complete_correction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (f : ℝ → ℝ)
    (hf : HasPDF (μ.map X) f) :
    (∀ t : ℝ, μ {ω | X ω = t} = 0) ∧
    ¬ (Set.range X).Countable ∧ ¬ Countable Ω ∧
    (let C : Set ℝ := Set.Icc (0 : ℝ) (1 / 2) \ Set.range (fun q : ℚ => (q : ℝ))
     ∃ ν : Measure C,
       MeasurableSet C ∧ volume C = 1 / 2 ∧ IsProbabilityMeasure ν ∧
       Measurable (fun x : C => (x : ℝ)) ∧
       Set.range (fun x : C => (x : ℝ)) = C ∧
       HasPDF (ν.map (fun x : C => (x : ℝ))) (fun x => if x ∈ C then 2 else 0) ∧
       ¬ C.Countable ∧ ¬ Countable C ∧
       ∀ a b : ℝ, a < b → ¬ Set.Icc a b ⊆ Set.range (fun x : C => (x : ℝ))) :=
  IrrationalRange.assemble IrrationalRange.n1_proof IrrationalRange.n2_proof
    IrrationalRange.n3_proof IrrationalRange.n4_proof μ X hX f hf

end
end AronowAudit.P001.Wave1
