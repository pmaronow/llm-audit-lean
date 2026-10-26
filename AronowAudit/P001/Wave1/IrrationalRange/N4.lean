import AronowAudit.P001.Wave1.IrrationalRangeBlueprint
import AronowAudit.P001.Wave1.IrrationalRange.N1

namespace AronowAudit.P001.Wave1.IrrationalRange

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableIrrationalRangeN4 (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem n4_proof : N4 := by
  have hC : MeasurableSet irrHalf := n1_proof.1
  have hd : irrHalfDensity = irrHalf.indicator (fun _ => (2 : ℝ)) := by
    funext x
    by_cases hx : x ∈ irrHalf
    · have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 2) \ Set.range (fun q : ℚ => (q : ℝ)) := hx
      simp only [irrHalfDensity, if_pos hx', Set.indicator_of_mem hx]
    · have hx' : x ∉ Set.Icc (0 : ℝ) (1 / 2) \ Set.range (fun q : ℚ => (q : ℝ)) := hx
      simp only [irrHalfDensity, if_neg hx', Set.indicator_of_notMem hx]
  have hm : Measurable irrHalfDensity := by
    rw [hd]
    exact measurable_const.indicator hC
  refine ⟨hm.aemeasurable, ?_⟩
  rw [hd]
  apply IntegrableOn.integrable_indicator _ hC
  exact integrableOn_const (by rw [n1_proof.2.1]; norm_num)

end
end AronowAudit.P001.Wave1.IrrationalRange
